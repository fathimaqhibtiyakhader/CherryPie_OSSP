/*
 * Linux Process Management + Task Manager Style Monitor
 *
 * Original concepts retained:
 *   fork(), getpid(), getppid(), exec(), wait(), waitpid(),
 *   exit(), kill(), signals, zombie and orphan processes.
 *
 * Added:
 *   - Live /proc process table
 *   - PID / PPID and process state
 *   - CPU time (user + kernel ticks and seconds)
 *   - RAM (RSS), virtual memory, data/stack/executable memory
 *   - Number of threads
 *   - Command / executable name
 *   - Process tree (parent -> children)
 *   - Parent-chain backtracking
 *   - Direct children listing
 *   - Detailed information for any PID
 *   - Process snapshot with CPU/RAM information
 *
 * Linux only: the monitor uses the Linux /proc filesystem.
 *
 * Compile:
 *   gcc -O2 -Wall -Wextra -o process_system process_system.c
 *
 * Run:
 *   ./process_system
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <signal.h>
#include <string.h>
#include <errno.h>
#include <dirent.h>
#include <ctype.h>
#include <limits.h>
#include <time.h>
#include <stdint.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <semaphore.h>

#define MAX_PROCESSES 8192
#define MAX_LINE 4096
#define MAX_NAME 256
#define MAX_TREE_DEPTH 64

typedef struct {
    pid_t pid;
    pid_t ppid;
    char state;
    char name[MAX_NAME];
    char cmdline[MAX_LINE];

    unsigned long utime;
    unsigned long stime;
    unsigned long num_threads;

    unsigned long vsize_kb;
    long rss_kb;
    long shared_kb;
    long text_kb;
    long data_kb;
    long stack_kb;

    unsigned long minflt;
    unsigned long majflt;
    unsigned long voluntary_ctxt;
    unsigned long nonvoluntary_ctxt;
} ProcessInfo;

/* =========================================================
   COMMON HELPERS
   ========================================================= */

static void print_separator(int n)
{
    for (int i = 0; i < n; ++i)
        putchar('-');
    putchar('\n');
}

static int is_numeric_string(const char *s)
{
    if (s == NULL || *s == '\0')
        return 0;

    for (; *s; ++s)
        if (!isdigit((unsigned char)*s))
            return 0;

    return 1;
}

static long get_page_size_kb(void)
{
    long page = sysconf(_SC_PAGESIZE);
    if (page <= 0)
        page = 4096;
    return page / 1024;
}

static long get_clock_ticks(void)
{
    long ticks = sysconf(_SC_CLK_TCK);
    return ticks > 0 ? ticks : 100;
}

static void safe_read_cmdline(pid_t pid, char *out, size_t out_size)
{
    char path[64];
    int fd;
    ssize_t n;

    if (out_size == 0)
        return;

    out[0] = '\0';

    snprintf(path, sizeof(path), "/proc/%d/cmdline", pid);
    fd = open(path, 0);

    if (fd < 0)
        return;

    n = read(fd, out, out_size - 1);
    close(fd);

    if (n <= 0)
        return;

    out[n] = '\0';

    /* /proc/PID/cmdline separates arguments with NUL characters. */
    for (ssize_t i = 0; i < n - 1; ++i) {
        if (out[i] == '\0')
            out[i] = ' ';
    }
}

static void print_bytes_kb(long long kb)
{
    if (kb < 0) {
        printf("N/A");
        return;
    }

    if (kb >= 1024LL * 1024LL)
        printf("%.2f GB", kb / (1024.0 * 1024.0));
    else if (kb >= 1024LL)
        printf("%.2f MB", kb / 1024.0);
    else
        printf("%lld KB", kb);
}

/* =========================================================
   /PROC PARSING
   ========================================================= */

static int read_process_stat(pid_t pid, ProcessInfo *p)
{
    char path[64];
    char line[MAX_LINE];
    FILE *fp;

    snprintf(path, sizeof(path), "/proc/%d/stat", pid);
    fp = fopen(path, "r");

    if (!fp)
        return 0;

    if (!fgets(line, sizeof(line), fp)) {
        fclose(fp);
        return 0;
    }

    fclose(fp);

    /*
     * comm is between the first '(' and the LAST ')'.
     * This is important because a process name can contain ')'.
     */
    char *left = strchr(line, '(');
    char *right = strrchr(line, ')');

    if (!left || !right || right <= left)
        return 0;

    size_t name_len = (size_t)(right - left - 1);
    if (name_len >= sizeof(p->name))
        name_len = sizeof(p->name) - 1;

    memcpy(p->name, left + 1, name_len);
    p->name[name_len] = '\0';

    char *rest = right + 2; /* skip ") " */
    char state;
    long long ppid_ll;
    unsigned long dummy_ulong;

    /*
     * Fields after comm:
     * 3 state
     * 4 ppid
     * ...
     * 10 minflt
     * 12 majflt
     * 14 utime
     * 15 stime
     * 20 num_threads
     * 23 vsize
     * 24 rss
     */
    int matched = sscanf(
        rest,
        "%c %lld "
        "%*d %*d %*d %*d %*d %*d "
        "%lu %*u %lu "
        "%*u %*u %lu %lu "
        "%*d %*d %*d %*d %lu "
        "%lu %ld",
        &state,
        &ppid_ll,
        &p->minflt,
        &p->majflt,
        &p->utime,
        &p->stime,
        &p->num_threads,
        &p->vsize_kb,
        &p->rss_kb
    );

    /*
     * The sscanf layout above is intentionally conservative. If a kernel
     * exposes a different layout, fall back to token parsing.
     */
    if (matched < 9) {
        char *saveptr = NULL;
        char *token = strtok_r(rest, " ", &saveptr);
        unsigned long long fields[64];
        char state2 = '\0';
        int idx = 0;

        if (!token) return 0;
        state2 = token[0];

        token = strtok_r(NULL, " ", &saveptr);
        if (!token) return 0;
        ppid_ll = strtoll(token, NULL, 10);

        idx = 0;
        while ((token = strtok_r(NULL, " ", &saveptr)) != NULL && idx < 64) {
            fields[idx++] = strtoull(token, NULL, 10);
        }

        /* fields[0] = session (field 5), so:
           field 10 -> fields[5]
           field 12 -> fields[7]
           field 14 -> fields[11]
           field 15 -> fields[12]
           field 20 -> fields[17]
           field 23 -> fields[20]
           field 24 -> fields[21] */
        if (idx <= 21)
            return 0;

        state = state2;
        p->minflt = (unsigned long)fields[5];
        p->majflt = (unsigned long)fields[7];
        p->utime = (unsigned long)fields[11];
        p->stime = (unsigned long)fields[12];
        p->num_threads = (unsigned long)fields[17];
        p->vsize_kb = (unsigned long)(fields[20] / 1024ULL);
        p->rss_kb = (long)(fields[21] * (unsigned long long)get_page_size_kb());
    }

    p->pid = pid;
    p->ppid = (pid_t)ppid_ll;
    p->state = state;

    /* Silence an otherwise unused temporary on some compilers. */
    dummy_ulong = 0;
    (void)dummy_ulong;

    safe_read_cmdline(pid, p->cmdline, sizeof(p->cmdline));

    if (p->cmdline[0] == '\0')
        snprintf(p->cmdline, sizeof(p->cmdline), "[%s]", p->name);

    return 1;
}

static void read_process_status_memory(pid_t pid, ProcessInfo *p)
{
    char path[64];
    char line[MAX_LINE];
    FILE *fp;

    p->shared_kb = -1;
    p->text_kb = -1;
    p->data_kb = -1;
    p->stack_kb = -1;
    p->voluntary_ctxt = 0;
    p->nonvoluntary_ctxt = 0;

    snprintf(path, sizeof(path), "/proc/%d/status", pid);
    fp = fopen(path, "r");
    if (!fp)
        return;

    while (fgets(line, sizeof(line), fp)) {
        if (sscanf(line, "VmRSS: %ld kB", &p->rss_kb) == 1)
            continue;
        if (sscanf(line, "VmSize: %lu kB", &p->vsize_kb) == 1)
            continue;
        if (sscanf(line, "VmData: %ld kB", &p->data_kb) == 1)
            continue;
        if (sscanf(line, "VmStk: %ld kB", &p->stack_kb) == 1)
            continue;
        if (sscanf(line, "VmExe: %ld kB", &p->text_kb) == 1)
            continue;
        if (sscanf(line, "RssShmem: %ld kB", &p->shared_kb) == 1)
            continue;
        if (sscanf(line, "Threads: %lu", &p->num_threads) == 1)
            continue;
        if (sscanf(line, "voluntary_ctxt_switches: %lu",
                   &p->voluntary_ctxt) == 1)
            continue;
        if (sscanf(line, "nonvoluntary_ctxt_switches: %lu",
                   &p->nonvoluntary_ctxt) == 1)
            continue;
    }

    fclose(fp);
}

static int read_process_info(pid_t pid, ProcessInfo *p)
{
    memset(p, 0, sizeof(*p));

    if (!read_process_stat(pid, p))
        return 0;

    read_process_status_memory(pid, p);
    return 1;
}

static int collect_processes(ProcessInfo *list, int max)
{
    DIR *dir = opendir("/proc");
    struct dirent *entry;
    int count = 0;

    if (!dir) {
        perror("opendir /proc");
        return 0;
    }

    while ((entry = readdir(dir)) != NULL && count < max) {
        if (!is_numeric_string(entry->d_name))
            continue;

        pid_t pid = (pid_t)strtol(entry->d_name, NULL, 10);

        if (read_process_info(pid, &list[count]))
            count++;
    }

    closedir(dir);
    return count;
}

/* =========================================================
   PROCESS TREE / BACKTRACKING
   ========================================================= */

static const ProcessInfo *find_process(const ProcessInfo *list, int count,
                                       pid_t pid)
{
    for (int i = 0; i < count; ++i)
        if (list[i].pid == pid)
            return &list[i];

    return NULL;
}

static void print_process_row(const ProcessInfo *p, int index)
{
    double cpu_seconds =
        (double)(p->utime + p->stime) / (double)get_clock_ticks();

    printf("%-5d %-7d %-7d %-3c %-9.1f ",
           index, (int)p->pid, (int)p->ppid, p->state, cpu_seconds);

    if (p->rss_kb >= 0)
        printf("%-10ld ", p->rss_kb);
    else
        printf("%-10s ", "N/A");

    if (p->vsize_kb > 0)
        printf("%-11lu ", p->vsize_kb);
    else
        printf("%-11s ", "N/A");

    printf("%-7lu ", p->num_threads);
    printf("%-22.22s\n", p->name);
}

static void print_process_header(void)
{
    printf("\n%-5s %-7s %-7s %-3s %-9s %-10s %-11s %-7s %-22s\n",
           "#", "PID", "PPID", "ST", "CPU(s)",
           "RSS(KB)", "VIRT(KB)", "THR", "NAME");
    print_separator(105);
}

static void display_all_processes(void)
{
    ProcessInfo *list =
        malloc(sizeof(ProcessInfo) * MAX_PROCESSES);

    if (!list) {
        perror("malloc");
        return;
    }

    int count = collect_processes(list, MAX_PROCESSES);

    printf("\n==============================================================\n");
    printf("              LIVE PROCESS LIST (/proc)\n");
    printf("==============================================================\n");
    printf("Processes visible to this user/system: %d\n", count);

    print_process_header();

    for (int i = 0; i < count; ++i)
        print_process_row(&list[i], i + 1);

    free(list);
}

static void print_tree_recursive(const ProcessInfo *list, int count,
                                 pid_t parent, int depth)
{
    if (depth >= MAX_TREE_DEPTH)
        return;

    for (int i = 0; i < count; ++i) {
        if (list[i].ppid != parent)
            continue;

        for (int d = 0; d < depth; ++d)
            printf("    ");

        printf("|-- PID %-6d [%c] %s",
               (int)list[i].pid, list[i].state, list[i].name);

        printf("  RSS=");
        print_bytes_kb(list[i].rss_kb);
        printf("  VIRT=");
        print_bytes_kb((long long)list[i].vsize_kb);
        printf("  Threads=%lu\n", list[i].num_threads);

        print_tree_recursive(list, count, list[i].pid, depth + 1);
    }
}

static void display_process_tree(void)
{
    ProcessInfo *list =
        malloc(sizeof(ProcessInfo) * MAX_PROCESSES);

    if (!list) {
        perror("malloc");
        return;
    }

    int count = collect_processes(list, MAX_PROCESSES);

    printf("\n==============================================================\n");
    printf("                    PROCESS TREE\n");
    printf("==============================================================\n");
    printf("This shows PPID relationships, so you can backtrack processes.\n\n");

    /* PID 1 is normally the root of the Linux userspace tree. */
    const ProcessInfo *init = find_process(list, count, 1);

    if (init) {
        printf("PID 1 [%c] %s  RSS=", init->state, init->name);
        print_bytes_kb(init->rss_kb);
        printf("\n");
        print_tree_recursive(list, count, 1, 1);
    } else {
        printf("PID 1 is not visible. Showing processes with missing parents:\n");

        for (int i = 0; i < count; ++i) {
            if (!find_process(list, count, list[i].ppid)) {
                printf("PID %d [%c] %s (PPID %d)\n",
                       (int)list[i].pid, list[i].state,
                       list[i].name, (int)list[i].ppid);
                print_tree_recursive(list, count, list[i].pid, 1);
            }
        }
    }

    free(list);
}

static void display_parent_chain(pid_t pid)
{
    ProcessInfo *list =
        malloc(sizeof(ProcessInfo) * MAX_PROCESSES);

    if (!list) {
        perror("malloc");
        return;
    }

    int count = collect_processes(list, MAX_PROCESSES);
    const ProcessInfo *current = find_process(list, count, pid);

    if (!current) {
        printf("PID %d is not accessible or no longer exists.\n", (int)pid);
        free(list);
        return;
    }

    printf("\n==============================================================\n");
    printf("                 PARENT-CHAIN BACKTRACK\n");
    printf("==============================================================\n");

    int guard = 0;

    while (current && guard++ < MAX_TREE_DEPTH) {
        printf("PID %-7d PPID %-7d [%c] %-25s RSS=",
               (int)current->pid,
               (int)current->ppid,
               current->state,
               current->name);

        print_bytes_kb(current->rss_kb);
        printf(" VIRT=");
        print_bytes_kb((long long)current->vsize_kb);
        printf("\n");

        if (current->ppid <= 0 || current->ppid == current->pid)
            break;

        current = find_process(list, count, current->ppid);
    }

    if (!current)
        printf("Parent is no longer visible in /proc.\n");

    free(list);
}

static void display_children(pid_t pid)
{
    ProcessInfo *list =
        malloc(sizeof(ProcessInfo) * MAX_PROCESSES);

    if (!list) {
        perror("malloc");
        return;
    }

    int count = collect_processes(list, MAX_PROCESSES);
    int found = 0;

    printf("\n==============================================================\n");
    printf("                    CHILD PROCESSES\n");
    printf("==============================================================\n");

    print_process_header();

    for (int i = 0; i < count; ++i) {
        if (list[i].ppid == pid) {
            found = 1;
            print_process_row(&list[i], i + 1);
        }
    }

    if (!found)
        printf("No currently visible direct children for PID %d.\n", (int)pid);

    free(list);
}

/* =========================================================
   DETAILED PROCESS INFORMATION
   ========================================================= */

static void display_process_details(pid_t pid)
{
    ProcessInfo p;

    if (!read_process_info(pid, &p)) {
        printf("Unable to read PID %d. It may have exited or permission "
               "may be restricted.\n", (int)pid);
        return;
    }

    double user_sec = (double)p.utime / get_clock_ticks();
    double kernel_sec = (double)p.stime / get_clock_ticks();
    double total_sec = user_sec + kernel_sec;

    printf("\n==============================================================\n");
    printf("                DETAILED PROCESS INFORMATION\n");
    printf("==============================================================\n");

    printf("Process name       : %s\n", p.name);
    printf("PID                : %d\n", (int)p.pid);
    printf("Parent PID (PPID)  : %d\n", (int)p.ppid);
    printf("State              : %c\n", p.state);
    printf("Command            : %s\n", p.cmdline);

    printf("\n--- CPU / EXECUTION ---\n");
    printf("User CPU ticks     : %lu\n", p.utime);
    printf("Kernel CPU ticks   : %lu\n", p.stime);
    printf("User CPU time      : %.3f seconds\n", user_sec);
    printf("Kernel CPU time    : %.3f seconds\n", kernel_sec);
    printf("Total CPU time     : %.3f seconds\n", total_sec);
    printf("System clock ticks : %ld ticks/sec\n", get_clock_ticks());

    printf("\n--- MEMORY ---\n");
    printf("Virtual memory     : ");
    print_bytes_kb((long long)p.vsize_kb);
    printf(" (%lu KB)\n", p.vsize_kb);

    printf("Resident RAM (RSS) : ");
    print_bytes_kb(p.rss_kb);
    printf("\n");

    printf("Shared memory      : ");
    print_bytes_kb(p.shared_kb);
    printf("\n");

    printf("Executable memory  : ");
    print_bytes_kb(p.text_kb);
    printf("\n");

    printf("Data memory        : ");
    print_bytes_kb(p.data_kb);
    printf("\n");

    printf("Stack memory       : ");
    print_bytes_kb(p.stack_kb);
    printf("\n");

    printf("\n--- THREADS / CONTEXT ---\n");
    printf("Threads            : %lu\n", p.num_threads);
    printf("Voluntary switches : %lu\n", p.voluntary_ctxt);
    printf("Non-voluntary sw.  : %lu\n", p.nonvoluntary_ctxt);

    printf("\n--- PAGE FAULTS ---\n");
    printf("Minor page faults  : %lu\n", p.minflt);
    printf("Major page faults  : %lu\n", p.majflt);

    printf("\n--- PROCESS RELATIONSHIP ---\n");
    display_parent_chain(pid);
}

/* =========================================================
   SYSTEM SUMMARY
   ========================================================= */

static void display_system_summary(void)
{
    FILE *fp;
    char line[MAX_LINE];

    unsigned long long total_kb = 0;
    unsigned long long free_kb = 0;
    unsigned long long available_kb = 0;

    fp = fopen("/proc/meminfo", "r");
    if (fp) {
        while (fgets(line, sizeof(line), fp)) {
            sscanf(line, "MemTotal: %llu kB", &total_kb);
            sscanf(line, "MemFree: %llu kB", &free_kb);
            sscanf(line, "MemAvailable: %llu kB", &available_kb);
        }
        fclose(fp);
    }

    ProcessInfo *list =
        malloc(sizeof(ProcessInfo) * MAX_PROCESSES);

    if (!list)
        return;

    int count = collect_processes(list, MAX_PROCESSES);

    unsigned long long total_rss = 0;
    unsigned long long total_virtual = 0;

    for (int i = 0; i < count; ++i) {
        if (list[i].rss_kb > 0)
            total_rss += (unsigned long long)list[i].rss_kb;

        total_virtual += list[i].vsize_kb;
    }

    printf("\n==============================================================\n");
    printf("                    SYSTEM SUMMARY\n");
    printf("==============================================================\n");

    printf("Visible processes     : %d\n", count);

    printf("Physical RAM total    : ");
    print_bytes_kb((long long)total_kb);
    printf("\n");

    printf("Physical RAM free     : ");
    print_bytes_kb((long long)free_kb);
    printf("\n");

    printf("Physical RAM available: ");
    print_bytes_kb((long long)available_kb);
    printf("\n");

    printf("Sum of process RSS    : ");
    print_bytes_kb((long long)total_rss);
    printf("\n");

    printf("Sum of virtual memory : ");
    print_bytes_kb((long long)total_virtual);
    printf("\n");

    printf("\nNote: process RSS values are not necessarily additive in the\n");
    printf("same way as physical memory because pages can be shared.\n");

    free(list);
}

/* =========================================================
   ORIGINAL DEMONSTRATIONS
   ========================================================= */

static void print_status(int status)
{
    if (WIFEXITED(status)) {
        printf("[Parent] Child exited normally with status = %d\n",
               WEXITSTATUS(status));
    } else if (WIFSIGNALED(status)) {
        printf("[Parent] Child terminated by signal = %d\n",
               WTERMSIG(status));
    } else if (WIFSTOPPED(status)) {
        printf("[Parent] Child stopped by signal = %d\n",
               WSTOPSIG(status));
    }
}

/* ---------------------------------------------------------
   1. PROCESS CREATION
   --------------------------------------------------------- */

static void process_creation(void)
{
    printf("\n========================================\n");
    printf("       PROCESS CREATION\n");
    printf("========================================\n");

    pid_t pid = fork();

    if (pid < 0) {
        perror("fork failed");
        return;
    }

    if (pid == 0) {
        printf("[Child]\n");
        printf("PID  = %d\n", getpid());
        printf("PPID = %d\n", getppid());
        printf("[Child] Process created successfully.\n");
        exit(0);
    } else {
        int status;

        printf("[Parent]\n");
        printf("PID       = %d\n", getpid());
        printf("Child PID = %d\n", pid);

        waitpid(pid, &status, 0);

        printf("[Parent] Child process completed.\n");
        print_status(status);
    }
}

/* ---------------------------------------------------------
   2. EXECUTION USING EXEC()
   --------------------------------------------------------- */

static void process_execution(void)
{
    printf("\n========================================\n");
    printf("       PROCESS EXECUTION\n");
    printf("========================================\n");

    pid_t pid = fork();

    if (pid < 0) {
        perror("fork failed");
        return;
    }

    if (pid == 0) {
        printf("[Child] PID = %d\n", getpid());
        printf("[Child] Executing 'ls -l' using exec().\n\n");

        execl("/bin/ls", "ls", "-l", NULL);

        perror("exec failed");
        exit(EXIT_FAILURE);
    } else {
        int status;

        printf("[Parent] Waiting for child PID %d...\n", pid);

        waitpid(pid, &status, 0);

        printf("[Parent] exec child finished.\n");
        print_status(status);
    }
}

/* ---------------------------------------------------------
   3. WAIT() SYNCHRONIZATION
   --------------------------------------------------------- */

static void process_synchronization(void)
{
    printf("\n========================================\n");
    printf("       PROCESS SYNCHRONIZATION\n");
    printf("========================================\n");

    pid_t pid = fork();

    if (pid < 0) {
        perror("fork failed");
        return;
    }

    if (pid == 0) {
        printf("[Child] PID = %d\n", getpid());
        printf("[Child] Working for 3 seconds...\n");

        sleep(3);

        printf("[Child] Work completed.\n");
        exit(42);
    } else {
        int status;

        printf("[Parent] Waiting using waitpid()...\n");

        waitpid(pid, &status, 0);

        printf("[Parent] Child has finished.\n");

        if (WIFEXITED(status)) {
            printf("[Parent] Exit status received = %d\n",
                   WEXITSTATUS(status));
        }
    }
}

/* ---------------------------------------------------------
   4. SIGNAL AND KILL()
   --------------------------------------------------------- */

static volatile sig_atomic_t signal_received = 0;

static void signal_handler(int signal)
{
    signal_received = signal;
    printf("\n[Child] Signal %d received!\n", signal);

    if (signal == SIGTERM) {
        printf("[Child] Termination signal received.\n");
        printf("[Child] Exiting safely...\n");
    }
}

static void signal_control(void)
{
    printf("\n========================================\n");
    printf("       SIGNAL / PROCESS CONTROL\n");
    printf("========================================\n");

    pid_t pid = fork();

    if (pid < 0) {
        perror("fork failed");
        return;
    }

    if (pid == 0) {
        signal(SIGTERM, signal_handler);

        printf("[Child] PID = %d\n", getpid());
        printf("[Child] Waiting for SIGTERM...\n");

        while (!signal_received)
            sleep(1);

        exit(0);
    } else {
        printf("[Parent] Child PID = %d\n", pid);

        sleep(2);

        printf("[Parent] Sending SIGTERM using kill()...\n");

        if (kill(pid, SIGTERM) == -1)
            perror("kill failed");

        int status;
        waitpid(pid, &status, 0);

        printf("[Parent] Signal-controlled child terminated.\n");
        print_status(status);
    }
}

/* ---------------------------------------------------------
   5. EXPLICIT TERMINATION USING EXIT()
   --------------------------------------------------------- */

static void process_termination(void)
{
    printf("\n========================================\n");
    printf("       PROCESS TERMINATION\n");
    printf("========================================\n");

    pid_t pid = fork();

    if (pid < 0) {
        perror("fork failed");
        return;
    }

    if (pid == 0) {
        printf("[Child] PID = %d\n", getpid());
        printf("[Child] Performing some work...\n");

        sleep(2);

        printf("[Child] Calling exit(10)...\n");
        exit(10);
    } else {
        int status;

        waitpid(pid, &status, 0);

        printf("[Parent] Child termination detected.\n");

        if (WIFEXITED(status)) {
            printf("[Parent] Child exit status = %d\n",
                   WEXITSTATUS(status));
        }
    }
}

/* ---------------------------------------------------------
   6. ZOMBIE PROCESS
   --------------------------------------------------------- */

static void zombie_process(void)
{
    printf("\n========================================\n");
    printf("          ZOMBIE PROCESS\n");
    printf("========================================\n");

    pid_t pid = fork();

    if (pid < 0) {
        perror("fork failed");
        return;
    }

    if (pid == 0) {
        printf("[Child] PID = %d\n", getpid());
        printf("[Child] Exiting immediately...\n");
        exit(0);
    } else {
        printf("[Parent] PID = %d\n", getpid());
        printf("[Parent] Child PID = %d\n", pid);

        printf("[Parent] Sleeping for 10 seconds.\n");
        printf("[Parent] During this time the child becomes a ZOMBIE.\n");

        printf("\nYou can now use the Task Manager menu and inspect PID %d.\n\n",
               (int)pid);

        sleep(10);

        waitpid(pid, NULL, 0);

        printf("[Parent] Zombie child has now been reaped.\n");
    }
}

/* ---------------------------------------------------------
   7. ORPHAN PROCESS
   --------------------------------------------------------- */

static void orphan_process(void)
{
    printf("\n========================================\n");
    printf("          ORPHAN PROCESS\n");
    printf("========================================\n");

    pid_t pid = fork();

    if (pid < 0) {
        perror("fork failed");
        return;
    }

    if (pid == 0) {
        printf("[Child] Original PID  = %d\n", getpid());
        printf("[Child] Original PPID = %d\n", getppid());

        printf("[Child] Sleeping while parent exits...\n");

        sleep(5);

        printf("\n[Child] Parent has terminated.\n");
        printf("[Child] New PPID = %d\n", getppid());

        printf("[Child] I am now an orphan process.\n");

        exit(0);
    } else {
        printf("[Parent] PID = %d\n", getpid());
        printf("[Parent] Child PID = %d\n", pid);

        printf("[Parent] Exiting before child...\n");

        exit(0);
    }
}

/* =========================================================
   EXTENDED LINUX OS FEATURES
   ========================================================= */

static void report_operation(const char *command,
                            const char *syscall_name,
                            pid_t pid,
                            const char *target,
                            unsigned long impact_bytes,
                            int success,
                            const char *detail)
{
    printf("Command: %-18s | API: %-12s | PID: %-6d | Target: %-30s | Impact: %-8lu B | %s | %s\n",
           command,
           syscall_name,
           (int)pid,
           target,
           impact_bytes,
           success ? "SUCCESS" : "FAILURE",
           detail ? detail : "status");
}

static void display_resource_report(const char *label, pid_t pid, const char *file_path)
{
    ProcessInfo p;
    struct stat st;
    long page_size = sysconf(_SC_PAGESIZE);
    unsigned long long rss_pages = 0;
    unsigned long long vsize_pages = 0;

    printf("\n==============================================================\n");
    printf("                  RESOURCE REPORT: %s\n", label);
    printf("==============================================================\n");

    if (read_process_info(pid, &p)) {
        printf("Process     : PID=%d PPID=%d Name=%s State=%c\n",
               (int)p.pid, (int)p.ppid, p.name, p.state);
        printf("Virtual mem : %lu KB\n", p.vsize_kb);
        printf("RSS         : %ld KB\n", p.rss_kb);
        printf("Threads     : %lu\n", p.num_threads);
        printf("Page size   : %ld bytes\n", page_size);
        rss_pages = (unsigned long long)p.rss_kb * 1024ULL / (unsigned long long)page_size;
        vsize_pages = (unsigned long long)p.vsize_kb * 1024ULL / (unsigned long long)page_size;
        printf("RSS pages   : %llu\n", rss_pages);
        printf("VIRT pages  : %llu\n", vsize_pages);
        printf("Minor faults: %lu\n", p.minflt);
        printf("Major faults: %lu\n", p.majflt);
    } else {
        printf("Process info unavailable for PID %d\n", (int)pid);
    }

    if (file_path && stat(file_path, &st) == 0) {
        printf("File        : %s\n", file_path);
        printf("File size   : %lld bytes\n", (long long)st.st_size);
        printf("Permissions : %o\n", (unsigned int)(st.st_mode & 0777));
    }

    printf("--------------------------------------------------------------\n");
}

static void display_memory_layout(pid_t pid)
{
    ProcessInfo p;
    char maps_path[64];
    char line[MAX_LINE];
    long page_size = sysconf(_SC_PAGESIZE);
    unsigned long long total_mapped = 0;
    FILE *fp;

    printf("\n==============================================================\n");
    printf("                 MEMORY LAYOUT / PROC MAPS\n");
    printf("==============================================================\n");

    if (!read_process_info(pid, &p)) {
        printf("Unable to read PID %d.\n", (int)pid);
        return;
    }

    printf("PID            : %d\n", (int)p.pid);
    printf("PPID           : %d\n", (int)p.ppid);
    printf("Name           : %s\n", p.name);
    printf("State          : %c\n", p.state);
    printf("Text/code      : ");
    print_bytes_kb(p.text_kb);
    printf("\nData+heap      : ");
    print_bytes_kb(p.data_kb);
    printf("\nStack          : ");
    print_bytes_kb(p.stack_kb);
    printf("\nShared libs    : ");
    print_bytes_kb(p.shared_kb);
    printf("\nVirtual memory : ");
    print_bytes_kb((long long)p.vsize_kb);
    printf("\nRSS            : ");
    print_bytes_kb(p.rss_kb);
    printf("\nPage size      : %ld bytes\n", page_size);
    printf("RSS pages      : %llu\n",
           (unsigned long long)p.rss_kb * 1024ULL / (unsigned long long)page_size);
    printf("Virtual pages  : %llu\n",
           (unsigned long long)p.vsize_kb * 1024ULL / (unsigned long long)page_size);
    printf("Minor faults   : %lu\n", p.minflt);
    printf("Major faults   : %lu\n", p.majflt);

    snprintf(maps_path, sizeof(maps_path), "/proc/%d/maps", (int)pid);
    fp = fopen(maps_path, "r");
    if (!fp) {
        perror("fopen /proc/maps");
        return;
    }

    printf("\nMapped regions (from /proc/%d/maps):\n", (int)pid);
    printf("%-18s %-6s %-10s %-8s %-8s %s\n", "RANGE", "PERMS", "SIZE", "OFFSET", "INODE", "PATH");

    while (fgets(line, sizeof(line), fp)) {
        char *range = strtok(line, " \t\n");
        char *perms = NULL;
        char *offset_str = NULL;
        char *inode = NULL;
        char *path = NULL;
        unsigned long long start = 0, end = 0, offset = 0;
        char *dash = NULL;

        if (!range)
            continue;

        dash = strchr(range, '-');
        if (!dash)
            continue;

        *dash = '\0';
        start = strtoull(range, NULL, 16);
        end = strtoull(dash + 1, NULL, 16);

        perms = strtok(NULL, " \t\n");
        offset_str = strtok(NULL, " \t\n");
        (void)strtok(NULL, " \t\n");
        inode = strtok(NULL, " \t\n");
        path = strtok(NULL, "\n");

        if (offset_str)
            offset = strtoull(offset_str, NULL, 16);

        if (!perms)
            continue;

        printf("%-18s %-6s %8llu KB %7llu %7s ",
               range,
               perms,
               (unsigned long long)(end - start) / 1024ULL,
               offset,
               inode ? inode : "-");

        if (path && path[0] != '\0')
            printf("%s\n", path);
        else
            printf("[anonymous]\n");

        total_mapped += (end - start);
    }

    fclose(fp);
    printf("Estimated mapped memory total : %llu KB\n", total_mapped / 1024ULL);
    printf("==============================================================\n\n");
}

static void demonstrate_file_storage(void)
{
    const char *file_path = "/tmp/process_lab_storage.txt";
    const char *message1 = "Linux OS lab\n";
    const char *message2 = " appended data\n";
    char buffer[256];
    int fd;
    ssize_t bytes_read;
    ssize_t bytes_written;
    struct stat st;

    printf("\n==============================================================\n");
    printf("                  FILE STORAGE AND I/O DEMO\n");
    printf("==============================================================\n");

    fd = open(file_path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd >= 0) {
        bytes_written = write(fd, message1, strlen(message1));
        report_operation("create file", "open/write", getpid(), file_path,
                         (unsigned long)(bytes_written > 0 ? bytes_written : 0),
                         bytes_written > 0, "create and initialize file");
        close(fd);
    } else {
        report_operation("create file", "open", getpid(), file_path, 0, 0, "write/truncate failed");
    }

    fd = open(file_path, O_RDONLY, 0);
    if (fd >= 0) {
        memset(buffer, 0, sizeof(buffer));
        bytes_read = read(fd, buffer, sizeof(buffer) - 1);
        report_operation("read file", "read", getpid(), file_path,
                         (unsigned long)(bytes_read > 0 ? bytes_read : 0),
                         bytes_read >= 0, "read initial file content");
        printf("File content: %s\n", buffer);
        close(fd);
    } else {
        report_operation("read file", "open", getpid(), file_path, 0, 0, "read failed");
    }

    fd = open(file_path, O_WRONLY | O_APPEND, 0644);
    if (fd >= 0) {
        bytes_written = write(fd, message2, strlen(message2));
        report_operation("append file", "open/write", getpid(), file_path,
                         (unsigned long)(bytes_written > 0 ? bytes_written : 0),
                         bytes_written > 0, "append file content");
        close(fd);
    } else {
        report_operation("append file", "open", getpid(), file_path, 0, 0, "append failed");
    }

    fd = open(file_path, O_RDWR, 0644);
    if (fd >= 0) {
        if (lseek(fd, 0, SEEK_SET) == (off_t)-1) {
            perror("lseek");
        }
        const char *updated = "UPDATED\n";
        bytes_written = write(fd, updated, strlen(updated));
        report_operation("modify file", "lseek/write", getpid(), file_path,
                         (unsigned long)(bytes_written > 0 ? bytes_written : 0),
                         bytes_written > 0, "replace beginning of file");
        close(fd);
    } else {
        report_operation("modify file", "open", getpid(), file_path, 0, 0, "modify failed");
    }

    if (stat(file_path, &st) == 0) {
        printf("Current file size     : %lld bytes\n", (long long)st.st_size);
        printf("Current permissions   : %o\n", (unsigned int)(st.st_mode & 0777));
        report_operation("stat file", "stat", getpid(), file_path,
                         (unsigned long)st.st_size, 1, "query file metadata");
    } else {
        report_operation("stat file", "stat", getpid(), file_path, 0, 0, "metadata unavailable");
    }

    fd = open(file_path, O_RDONLY, 0);
    if (fd >= 0) {
        struct stat file_stat;
        if (fstat(fd, &file_stat) == 0) {
            printf("fstat size           : %lld bytes\n", (long long)file_stat.st_size);
            printf("fstat permissions    : %o\n", (unsigned int)(file_stat.st_mode & 0777));
            report_operation("file metadata", "fstat", getpid(), file_path,
                             (unsigned long)file_stat.st_size, 1, "query descriptor metadata");
        }
        close(fd);
    }

    if (unlink(file_path) == 0) {
        report_operation("delete file", "unlink", getpid(), file_path, 0, 1, "remove file from storage");
    } else {
        report_operation("delete file", "unlink", getpid(), file_path, 0, 0, "delete failed");
    }

    display_resource_report("after file demo", getpid(), file_path);
}

static void ipc_signal_handler(int sig)
{
    (void)sig;
    printf("[IPC] signal handler received SIGUSR1 from sender\n");
}

static void demonstrate_ipc_and_sync(void)
{
    int pipefd[2];
    pid_t child;
    char message[] = "Message via pipe";
    char buffer[128];
    ssize_t bytes;
    int status;
    sem_t *sem = NULL;

    printf("\n==============================================================\n");
    printf("                 IPC + SYNCHRONIZATION DEMO\n");
    printf("==============================================================\n");

    if (pipe(pipefd) == -1) {
        perror("pipe");
        return;
    }

    child = fork();
    if (child < 0) {
        perror("fork");
        close(pipefd[0]);
        close(pipefd[1]);
        return;
    }

    if (child == 0) {
        close(pipefd[0]);
        signal(SIGUSR1, ipc_signal_handler);
        printf("[Child] sending pipe message to parent\n");
        bytes = write(pipefd[1], message, strlen(message));
        report_operation("pipe send", "write", getpid(), "pipe[1]", (unsigned long)(bytes > 0 ? bytes : 0),
                         bytes > 0, "message transmitted to parent");
        kill(getppid(), SIGUSR1);
        close(pipefd[1]);
        exit(0);
    }

    close(pipefd[1]);
    memset(buffer, 0, sizeof(buffer));
    bytes = read(pipefd[0], buffer, sizeof(buffer) - 1);
    if (bytes > 0) {
        buffer[bytes] = '\0';
        report_operation("pipe receive", "read", getpid(), "pipe[0]",
                         (unsigned long)bytes, 1, "data received from child");
        printf("[Parent] received message: %s\n", buffer);
    } else {
        report_operation("pipe receive", "read", getpid(), "pipe[0]", 0, 0, "message read failed");
    }

    kill(child, SIGUSR1);
    report_operation("signal send", "kill", getpid(), "SIGUSR1", 0, 1, "send signal to child");

    waitpid(child, &status, 0);
    printf("[Parent] child exit status: %d\n", status);

    sem_unlink("/process_lab_semaphore");
    sem = sem_open("/process_lab_semaphore", O_CREAT | O_EXCL, 0644, 0);
    if (sem == SEM_FAILED) {
        perror("sem_open");
        return;
    }

    child = fork();
    if (child == 0) {
        printf("[Child2] waiting on semaphore...\n");
        sem_wait(sem);
        printf("[Child2] semaphore acquired\n");
        report_operation("semaphore wait", "sem_wait", getpid(), "/process_lab_semaphore",
                         0, 1, "child synchronized successfully");
        sem_close(sem);
        exit(0);
    }

    sleep(1);
    printf("[Parent] posting semaphore\n");
    sem_post(sem);
    report_operation("semaphore post", "sem_post", getpid(), "/process_lab_semaphore",
                     0, 1, "parent releases synchronization token");
    waitpid(child, &status, 0);
    sem_close(sem);
    sem_unlink("/process_lab_semaphore");

    display_resource_report("after IPC / sync demo", getpid(), NULL);
}

static void demonstrate_memory_management(void)
{
    void *region_a = NULL;
    void *region_b = NULL;
    void *region_c = NULL;
    size_t bytes_a = 4096;
    size_t bytes_b = 256;

    printf("\n==============================================================\n");
    printf("                  MEMORY MANAGEMENT DEMO\n");
    printf("==============================================================\n");

    region_a = malloc(bytes_a);
    if (!region_a) {
        perror("malloc");
        return;
    }
    memset(region_a, 0xA5, bytes_a);
    report_operation("malloc", "malloc", getpid(), "heap block A", bytes_a, 1, "allocate 4 KB block");

    region_b = calloc(bytes_b, 16);
    if (!region_b) {
        perror("calloc");
        free(region_a);
        return;
    }
    memset(region_b, 0x5A, bytes_b * 16);
    report_operation("calloc", "calloc", getpid(), "heap block B", bytes_b * 16, 1, "allocate zero-initialized block");

    region_c = realloc(region_b, 512);
    if (!region_c) {
        perror("realloc");
        free(region_a);
        free(region_b);
        return;
    }
    region_b = region_c;
    report_operation("realloc", "realloc", getpid(), "heap block B", 512, 1, "resize memory region");

    printf("[Demo] Controlled leak prevention: allocate a temporary block, print status, then free it before exit.\n");
    void *temporary = malloc(1024);
    if (temporary) {
        memset(temporary, 0x7F, 1024);
        report_operation("temporary alloc", "malloc", getpid(), "temporary leak test", 1024, 1, "safe temporary block");
        free(temporary);
        temporary = NULL;
    }

    free(region_a);
    free(region_b);
    region_a = NULL;
    region_b = NULL;

    printf("[Demo] All allocations released; no active leak remains in the program.\n");
    display_resource_report("after memory management demo", getpid(), NULL);
}

static void run_extended_linux_demo(void)
{
    printf("\n==============================================================\n");
    printf("          EXTENDED LINUX OS DEMONSTRATION\n");
    printf("==============================================================\n");

    display_memory_layout(getpid());
    demonstrate_file_storage();
    demonstrate_ipc_and_sync();
    demonstrate_memory_management();
    display_system_summary();
}

/* =========================================================
   INPUT HANDLING
   ========================================================= */

static void clear_input_buffer(void);

/* =========================================================
   TASK MANAGER MENU
   ========================================================= */

static void task_manager_menu(void)
{
    while (1) {
        int choice;
        pid_t pid;

        printf("\n\n");
        printf("==============================================================\n");
        printf("             PROCESS TASK MANAGER / BACKTRACKER\n");
        printf("==============================================================\n");
        printf("1. Show all processes\n");
        printf("2. Show process tree\n");
        printf("3. Detailed information for a PID\n");
        printf("4. Backtrack parent chain of a PID\n");
        printf("5. Show direct children of a PID\n");
        printf("6. System memory/process summary\n");
        printf("0. Return to main menu\n");
        print_separator(62);
        printf("Enter choice: ");

        if (scanf("%d", &choice) != 1) {
            printf("Invalid input.\n");
            clear_input_buffer();
            continue;
        }

        clear_input_buffer();

        switch (choice) {
        case 1:
            display_all_processes();
            break;

        case 2:
            display_process_tree();
            break;

        case 3:
            printf("Enter PID: ");
            if (scanf("%d", &pid) == 1)
                display_process_details(pid);
            else {
                printf("Invalid PID.\n");
                clear_input_buffer();
            }
            clear_input_buffer();
            break;

        case 4:
            printf("Enter PID to backtrack: ");
            if (scanf("%d", &pid) == 1)
                display_parent_chain(pid);
            else {
                printf("Invalid PID.\n");
                clear_input_buffer();
            }
            clear_input_buffer();
            break;

        case 5:
            printf("Enter parent PID: ");
            if (scanf("%d", &pid) == 1)
                display_children(pid);
            else {
                printf("Invalid PID.\n");
                clear_input_buffer();
            }
            clear_input_buffer();
            break;

        case 6:
            display_system_summary();
            break;

        case 0:
            return;

        default:
            printf("Invalid choice.\n");
        }
    }
}

static void clear_input_buffer(void)
{
    int ch;
    while ((ch = getchar()) != '\n' && ch != EOF)
        ;
}

/* =========================================================
   MAIN MENU
   ========================================================= */

static void display_menu(void)
{
    printf("\n\n");
    printf("==============================================================\n");
    printf("        LINUX PROCESS MANAGEMENT + TASK MANAGER\n");
    printf("==============================================================\n");

    printf("1.  Process Creation\n");
    printf("2.  Process Execution using exec()\n");
    printf("3.  Process Synchronization\n");
    printf("4.  Signal / Process Control\n");
    printf("5.  Process Termination\n");
    printf("6.  Zombie Process Demonstration\n");
    printf("7.  Orphan Process Demonstration\n");
    printf("8.  Run Complete Demonstration\n");
    printf("9.  Open Process Task Manager / Backtracker\n");
    printf("10. Extended Linux OS Demo\n");
    printf("0.  Exit\n");

    print_separator(62);
    printf("Enter your choice: ");
}

int main(void)
{
    int choice;

    while (1) {
        display_menu();

        if (scanf("%d", &choice) != 1) {
            printf("Invalid input.\n");
            clear_input_buffer();
            continue;
        }

        clear_input_buffer();

        switch (choice) {
        case 1:
            process_creation();
            break;

        case 2:
            process_execution();
            break;

        case 3:
            process_synchronization();
            break;

        case 4:
            signal_control();
            break;

        case 5:
            process_termination();
            break;

        case 6:
            zombie_process();
            break;

        case 7:
            orphan_process();
            break;

        case 8:
            process_creation();
            process_execution();
            process_synchronization();
            signal_control();
            process_termination();
            zombie_process();
            orphan_process();
            printf("\nComplete demonstration finished.\n");
            break;

        case 9:
            task_manager_menu();
            break;

        case 10:
            run_extended_linux_demo();
            break;

        case 0:
            printf("\nExiting system...\n");
            printf("Goodbye!\n");
            return 0;

        default:
            printf("\nInvalid choice. Please try again.\n");
        }
    }

    return 0;
}
