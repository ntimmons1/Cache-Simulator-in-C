/* 
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss plus a possible eviction.
 *  2. Instruction loads (I) are ignored.
 *  3. Data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus a possible eviction.
 *
 * The function printSummary() is given to print output.
 * Please use this function to print the number of hits, misses and evictions.
 * This is crucial for the driver to evaluate your work.
 */

#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include <stdbool.h>

/****************************************************************************/
/***** DO NOT MODIFY THESE VARIABLE NAMES ***********************************/

/* Globals set by command line args */
int s = 0; /* set index bits */
int E = 0; /* associativity */
int b = 0; /* block offset bits */
int verbosity = 0; /* print trace if set */
char* trace_file = NULL;

/* Derived from command line args */
int B; /* block size (bytes) B = 2^b */
int S; /* number of sets S = 2^s In C, you can use the left shift operator */

/* Counters used to record cache statistics */
int hit_cnt = 0;
int miss_cnt = 0;
int evict_cnt = 0;
/*****************************************************************************/


/* Type: Memory address
 * Use this type whenever dealing with addresses or address masks
 */
typedef unsigned long long int mem_addr_t;

/* Type: Cache line
 */
typedef struct cache_line {
    char valid;
    mem_addr_t tag;
    int count;
} cache_line_t;

typedef cache_line_t* cache_set_t;
typedef cache_set_t* cache_t;


/* The cache we are simulating */
cache_t cache;

/*
 * initCache -
 * Allocate data structures to hold info regarding the sets and cache lines
 * use struct "cache_line_t" here
 * Initialize valid and tag field with 0s.
 */
void initCache() {
  S = 2 << (s-1);  // set number of sets for the cache
  cache = malloc(S * sizeof(cache_set_t));
  if (cache == NULL) {
        printf("Error: Cannot allocate cache");
        exit(1);
  }
  // allocate space for each set
  for (int i=0; i < S; i++){
    *(cache + i) = malloc(E * sizeof(cache_line_t));
    if (*(cache + i) == NULL) {
      printf("Cannot malloc cache_set.");
      exit(1);
    }
    // set tag and valid bits, update counter
    for (int j = 0; j < E; j++) {
      (*(cache + i) + j)->valid = '0';
      (*(cache + i) + j)->tag = 0;
      (*(cache + i) + j)->count = 0;
    }
  }
}


/*
 *deallocate all of the sets in cache, and then cache itself
 */
void freeCache() {
    for (int i = 0; i < S; i++) {
       free(*(cache + i));
    }

    free(cache);
}

/*
 * accessData - Access data at memory address addr.
 *   If it is already in cache, increase hit_cnt
 *   If it is not in cache, bring it in cache, increase miss count.
 *   Also increase evict_cnt if a line is evicted.
 */
void accessData(mem_addr_t addr) {
    int found = 0;  // non-zero if adress is found in cache, 0 if not

    // find the address' tag and set
    S = 2 << (s-1);
    B = 2 << (b-1);
    mem_addr_t addrTag = addr / (B * S);  // the extracted tag from 
    mem_addr_t setNum = (addr / B) % S;   // the extracted set number

    // find the most recent and least recently used blocks
    int mostRecent;  // keep track of the most recently used block
    int leastRecent;  // keep track of the least recently used block
    mostRecent = (*(cache + setNum) + 0)->count;
    leastRecent = (*(cache + setNum) + 0)->count;
    for (int n = 0; n < E; n++) {
        if (mostRecent < (*(cache + setNum) + n)->count) {
            mostRecent = (*(cache + setNum) + n)->count;
        }
        if (leastRecent > (*(cache + setNum) + n)->count) {
            leastRecent = (*(cache + setNum) + n)->count;
        }
    }

    // decide if it is possible to switch the least/most recent blocks
    for (int i = 0; i < E; i++) {
        if ((*(cache + setNum) + i)->tag == addrTag && 
           (*(cache + setNum) + i)->valid == '1') {
            hit_cnt++;
            found = 1;
            (*(cache + setNum) + i)->count = mostRecent + 1;
            mostRecent++;
            leastRecent++;
            for (int t = 0; t < E; t++) {
                if (leastRecent > (*(cache + setNum) + t)->count) {
                    leastRecent = (*(cache + setNum) + t)->count;
                }
            }
        }
    }

    // if the address isn't found, try to find in lower cache
    if (!found) {
        miss_cnt++;

        // if the cache has room,add the new block- update least/most recently
        for (int j = 0; j < E; j++) {
           if ((*(cache + setNum) + j)->valid == '0') {
               (*(cache + setNum) + j)->tag = addrTag;
               (*(cache + setNum) + j)->count = mostRecent + 1;
               mostRecent++;
               leastRecent++;
               (*(cache + setNum) + j)->valid = '1';
               found = 1;
               for (int t = 0; t < E; t++){
                   if (leastRecent > (*(cache + setNum) + t)->count) {
                        leastRecent = (*(cache + setNum) + t)->count;
                   }
               }
             break;
           }
        }

        // if the cache is full,put new block where the least recent one was
        if (!found) {
            for (int m = 0; m < E; m++) {
                 if ((*(cache + setNum) + m)->count == leastRecent) {
                    (*(cache + setNum) + m)->tag = addrTag;
                    (*(cache + setNum) + m)->count = mostRecent + 1;
                    mostRecent++;
                    leastRecent++;
                    evict_cnt++;
                    found = 1;
                    break;
                 } 
            }
        }
    } 
}

/*
 * replayTrace - replays the given trace file against the cache
 * reads the input trace file line by line
 * extracts the type of each memory access : L/S/M
 */
void replayTrace(char* trace_fn) {
    char buf[1000];  // char array to hold each line in file
    mem_addr_t address = 0;  // the address on each line
    unsigned int len = 0;  // length of each line
    FILE* trace_fp = fopen(trace_fn, "r");  // the initialized input file

    // if there is an error opening the file, print error message
    if (!trace_fp) {
        fprintf(stderr, "%s: %s\n", trace_fn, strerror(errno));
        exit(1);
    }

    // loop through file line by line
    while (fgets(buf, 1000, trace_fp) != NULL) {
        if (buf[1] == 'S' || buf[1] == 'L' || buf[1] == 'M') {
            sscanf(buf+3, "%llx,%u", &address, &len);

            if (verbosity)
                printf("%c %llx,%u ", buf[1], address, len);

            // call accessData function here depending on type of access
            if (buf[1] == 'S' || buf[1] == 'L') {
                 accessData(address);
            }

            if (buf[1] == 'M') {
                accessData(address);
                accessData(address);
            }
            if (verbosity)
                printf("\n");
        }
    }

    fclose(trace_fp);
}

/*
 * printUsage - Print usage info
 */
void printUsage(char* argv[]) {
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}

/*
 * printSummary - Summarize the cache simulation statistics.
 */
void printSummary(int hits, int misses, int evictions) {
    printf("hits:%d misses:%d evictions:%d\n", hits, misses, evictions);
    FILE* output_fp = fopen(".csim_results", "w");
    assert(output_fp);
    fprintf(output_fp, "%d %d %d\n", hits, misses, evictions);
    fclose(output_fp);
}

/*
 * main - Main routine
 */
int main(int argc, char* argv[]) {
    char c;

    // Parse the command line arguments: -h, -v, -s, -E, -b, -t
    while ((c = getopt(argc, argv, "s:E:b:t:vh")) != -1) {
        switch (c) {
            case 'b':
                b = atoi(optarg);
                break;
            case 'E':
                E = atoi(optarg);
                break;
            case 'h':
                printUsage(argv);
                exit(0);
            case 's':
                s = atoi(optarg);
                break;
            case 't':
                trace_file = optarg;
                break;
            case 'v':
                verbosity = 1;
                break;
            default:
                printUsage(argv);
                exit(1);
        }
    }

    /* Make sure that all required command line args were specified */
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("%s: Missing required command line argument\n", argv[0]);
        printUsage(argv);
        exit(1);
    }

    /* Initialize cache */
    initCache();

    replayTrace(trace_file);

    /* Free allocated memory */
    freeCache();

    /* Output the hit and miss statistics for the autograder */
    printSummary(hit_cnt, miss_cnt, evict_cnt);
    return 0;
}
