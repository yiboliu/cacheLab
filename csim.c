/* Name: Yibo Liu
 * CS login: yibol
 * Section: Lec 2
 *
 *
 *
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss. (I examined the trace,
 *  the largest request I saw was for 8 bytes).
 *  2. Instruction loads (I) are ignored, since we are interested in evaluating
 *  trans.c in terms of its data cache performance.
 *  3. data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus an possible eviction.
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

#include "cachelab.h"

// #define DEBUG_ON 
#define ADDRESS_LENGTH 64

/****************************************************************************/
/***** DO NOT MODIFY THESE VARIABLE NAMES ***********************************/

/* Globals set by command line args */
int verbosity = 0; /* print trace if set */
int s = 0; /* set index bits */
int b = 0; /* block offset bits */
int E = 0; /* associativity */
char* trace_file = NULL;

/* Derived from command line args */
int S; /* number of sets S = 2^s In C, you can use "pow" function*/
int B; /* block size (bytes) B = 2^b In C, you can use "pow" function*/

/* Counters used to record cache statistics */
int miss_count = 0;
int hit_count = 0;
int eviction_count = 0;
/*****************************************************************************/


/* Type: Memory address 
 * Use this type whenever dealing with addresses or address masks
  */
typedef unsigned long long int mem_addr_t;

/* Type: Cache line
 * TODO 
 * 
 * NOTE: 
 * You will need to add an extra field to this struct
 * depending on your implementation of the LRU policy for evicting a cache line
 * 
 * For example, to use a linked list based LRU,
 * you might want to have a field "struct cache_line * next" in the struct 
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

/* TODO - COMPLETE THIS FUNCTION
 * initCache - 
 * Allocate data structures to hold info regrading the sets and cache lines
 * use struct "cache_line_t" here
 * Initialize valid and tag field with 0s.
 * use S (= 2^s) and E while allocating the data structures here
 */
void initCache()
{
    // To get the value of S.
    S = pow(2, s);
    // Allocate the location for S cache_set_t's.
    cache = (cache_set_t*)malloc(sizeof(cache_set_t) * S);
    // Allocate the location for E cache_line_t's within each cache_set_t
    for (int set = 0; set < S; set++) {
        cache[set] = malloc(sizeof(cache_line_t) * E);
        for (int line = 0; line < E; line++) {
            cache[set][line].valid = 0;
            cache[set][line].tag = 0;
            cache[set][line].count = 0;
        }
    }
}


/* TODO - COMPLETE THIS FUNCTION 
 * freeCache - free each piece of memory you allocated using malloc 
 * inside initCache() function
 */
void freeCache()
{
    // Free each allocated location of cache_set-t
	S = pow(2 ,s);
    for (int set = 0; set < S; set++) {
        free((void*) cache[set]);
    }
    // Free the cache itself.
    free((void *) cache);
}


/* TODO - COMPLETE THIS FUNCTION 
 * accessData - Access data at memory address addr.
 *   If it is already in cache, increase hit_count
 *   If it is not in cache, bring it in cache, increase miss count.
 *   Also increase eviction_count if a line is evicted.
 *   you will manipulate data structures allocated in initCache() here
 */
void accessData(mem_addr_t addr)
{
    // get 1's for s bits
    mem_addr_t masks = pow(2, s) - 1;
    // shift the address rightward for b bits, so that the rightmost s bits make up the value of s
    mem_addr_t set = addr >> b;
    // bitwise AND the set with the masks to get the real value of S.
    set &= masks;
    // shift the address rightward for s+b bits, so that the address equals to the value of t
    mem_addr_t tg = addr >> (s + b);
    bool find = false;
    int maxCount = 0;

    // To find the max count.
    for (int k = 0; k < E; k++) {
        if (cache[set][k].count > maxCount){
            maxCount = cache[set][k].count;
        }
    }
    // Iterate through the set to find the valid line with corresponding tag
    for (int i = 0; i < E; i++) {
        if (cache[set][i].valid == 1 && cache[set][i].tag == tg) {
            hit_count++;
            find = true;
            cache[set][i].count = ++maxCount;
            return;
        }
    }
    // Go in this statement if it does not hit
    if (!find) {
        miss_count++;
        bool evict = true;
        for (int j = 0; j < E; j++) {
            // Find a line with 0 as valid and replace its tag with target tag.
            if(cache[set][j].valid == 0){         
                cache[set][j].tag = tg;
                cache[set][j].valid = 1;
                evict = false;
                cache[set][j].count = ++maxCount;
                return;
            }
        }
        if (evict) {
            eviction_count++;
            int minCount = cache[set][0].count;
            int toBeEvicted = 0;
            // To find the min count, and to find the line to replace.
            for (int l = 0; l < E; l++) {
                if (cache[set][l].count < minCount) {
                    minCount = cache[set][l].count;
                    toBeEvicted = l;
                }
            }
            // find the line to be evicted and do the corresponding replacement.
            cache[set][toBeEvicted].count = ++maxCount;
            cache[set][toBeEvicted].tag = tg;
        }
    }
}


/* TODO - FILL IN THE MISSING CODE
 * replayTrace - replays the given trace file against the cache 
 * reads the input trace file line by line
 * extracts the type of each memory access : L/S/M
 * YOU MUST TRANSLATE one "L" as a load i.e. 1 memory access
 * YOU MUST TRANSLATE one "S" as a store i.e. 1 memory access
 * YOU MUST TRANSLATE one "M" as a load followed by a store i.e. 2 memory accesses 
 */
void replayTrace(char* trace_fn)
{
    char buf[1000];
    mem_addr_t addr=0;
    unsigned int len=0;
    FILE* trace_fp = fopen(trace_fn, "r");

    if(!trace_fp){
        fprintf(stderr, "%s: %s\n", trace_fn, strerror(errno));
        exit(1);
    }

    while( fgets(buf, 1000, trace_fp) != NULL) {
        if(buf[1]=='S' || buf[1]=='L' || buf[1]=='M') {
            sscanf(buf+3, "%llx,%u", &addr, &len);
      
            if(verbosity)
                printf("%c %llx,%u", buf[1], addr, len);

           // TODO - MISSING CODE
           // now you have: 
           // 1. address accessed in variable - addr 
           // 2. type of acccess(S/L/M)  in variable - buf[1] 
           // call accessData function here depending on type of access
            // If to Store or Load, access data once.
            if (buf[1]=='S' || buf[1]=='L') accessData(addr);
            // If to modify data, access the data twice.
            if (buf[1]=='M') {
                accessData(addr);
                accessData(addr);
            }


            if (verbosity)
                printf(" \n");
        }
    }

    fclose(trace_fp);
}

/*
 * printUsage - Print usage info
 */
void printUsage(char* argv[])
{
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
 * main - Main routine 
 */
int main(int argc, char* argv[])
{
    char c;
    
    // Parse the command line arguments: -h, -v, -s, -E, -b, -t 
    while( (c=getopt(argc,argv,"s:E:b:t:vh")) != -1){
        switch(c){
        case 's':
            s = atoi(optarg);
            break;
        case 'E':
            E = atoi(optarg);
            break;
        case 'b':
            b = atoi(optarg);
            break;
        case 't':
            trace_file = optarg;
            break;
        case 'v':
            verbosity = 1;
            break;
        case 'h':
            printUsage(argv);
            exit(0);
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

#ifdef DEBUG_ON
    printf("DEBUG: S:%u E:%u B:%u trace:%s\n", S, E, B, trace_file);
#endif
 
    replayTrace(trace_file);

    /* Free allocated memory */
    freeCache();

    /* Output the hit and miss statistics for the autograder */
    printSummary(hit_count, miss_count, eviction_count);
    return 0;
}
