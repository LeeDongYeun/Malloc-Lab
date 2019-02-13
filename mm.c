/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "YEE",
    /* First member's full name */
    "Jaehyun, Ha",
    /* First member's email address */
    "jaehyunh1@kaist.ac.kr",
    /* Second member's full name (leave blank if none) */
    "Dongyeun, Lee",
    /* Second member's email address (leave blank if none) */
    "ledoye@kaist.ac.kr"
};

#define ALIGN(size) (((size) + (0x7) & ~0x7) //round up.
#define WSIZE 4 //word size
#define DSIZE 8 //data size          
#define CHUNKSIZE (1<<12) //4K.
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc)) //flag that represents both block size & if_allocated.
#define GET(p) (*(unsigned int *)(p)) //load address.
#define PUT(p,val) (*(unsigned int *)(p) = (val)) // save address.
#define GET_SIZE(p) (GET(p) & ~0x7) //get size.
#define GET_ALLOC(p) (GET(p) & 0x1) //get if_allocated.
#define HDRP(bp) ((char *)(bp) - WSIZE) // get header pointer.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)// get footer pointer.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //next block pointer.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //previous block pointer.
#define SUCC_LINK(bp) ((char *)(bp) + WSIZE) //next link pointer.(in lecture ppt 17 slide 9-14.)
#define PRED_LINK(bp) ((char *)(bp)) //previous link pointer.

static void *extend_heap(size_t words); //extending heap.
static void *coalesce(void *bp); // coalescing adjacent blocks
static void *find_fit(size_t asize); // first fit algorithm.
static void place(void *bp, size_t asize); // placing demanded blocks in appropriate location.
void insert_node(char *ptr); //insert the new block at the root of the list. (LIFO policy)
void normalize(char *ptr); //fixing the links.
char *heap_listp = NULL;
char *root = NULL;
int mm_check(void);

int mm_init(void){
	if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){ //take 4 words from system: then initialize.
		return -1;
	}
	PUT(heap_listp, 0);
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));
	root = heap_listp;
	heap_listp += (2 * WSIZE);
	
	if(extend_heap(CHUNKSIZE / WSIZE) == NULL){ // call extend_heap then extend the size of heap to 2^12.
		return -1;
	}
	
	return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * DSIZE : words * DSIZE;

    if((long)(bp = mem_sbrk(size)) == -1) // round up.
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); //freeing hdr
    PUT(FTRP(bp), PACK(size, 0)); //freeing ftr
    PUT(SUCC_LINK(bp), 0); //freeing next link
    PUT(PRED_LINK(bp), 0); //freeing prev link
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //new epilogue header.

    return coalesce(bp); //mix.
}

void *mm_malloc(size_t size){
    size_t asize; //adjusted size.
    size_t esize; // if it doesn't fits, extend it to CHUNKSIZE.
    char *bp;
    
	if(size <= 0){
		return NULL;
	} 

    if(size <= DSIZE){
        asize = 2 * DSIZE;
    }
    else{
        asize = DSIZE * ((size + DSIZE + DSIZE-1) / DSIZE); //adjusting.
    }
    if((bp = find_fit(asize)) != NULL){ //searching.
        place(bp, asize);
        return bp;
    }

    esize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(esize / DSIZE)) == NULL){ //placing.
        return NULL;
    }
    place(bp, asize);
    return bp;
}

void mm_free(void *ptr){
    	
	size_t size = GET_SIZE(HDRP(ptr));
   
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(SUCC_LINK(ptr), 0);
    PUT(PRED_LINK(ptr), 0);
    coalesce(ptr);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //if_allocated flags.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){ // prev and next allocated.
	}
	
    else if(prev_alloc && !next_alloc){ // prev allocated.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        normalize(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){ //next allocated.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        normalize(PREV_BLKP(bp));
        PUT(FTRP(bp),PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{ //both free.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        normalize(PREV_BLKP(bp));
        normalize(NEXT_BLKP(bp));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp);
    return bp;
}

void *mm_realloc(void *ptr, size_t size){
    if(size <= 0){ //equivalent to mm_free(ptr).
        mm_free(ptr);
        return 0;
    }

    if(ptr == NULL){
        return mm_malloc(size); //equivalent to mm_malloc(size).
    }

    void *newp = mm_malloc(size); //new pointer.

    if(newp == NULL){
        return 0;
    }
    
    size_t oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize){
    	oldsize = size; //shrink size.
	} 
    memcpy(newp, ptr, oldsize); //cover.
    mm_free(ptr);
    return newp;
}



void insert_node(char *ptr){
    char *SUCC = GET(root); //next pointer.
    if(SUCC != NULL){
	    PUT(PRED_LINK(SUCC), ptr); //if there exists next, ptr = previous link. 
	}
    PUT(SUCC_LINK(ptr), SUCC); //root -> next link.
    PUT(root, ptr);
}

void normalize(char *ptr){ //fixing the links.
	if(GET(PRED_LINK(ptr)) == NULL){
		if(GET(SUCC_LINK(ptr)) != NULL){
			PUT(PRED_LINK(GET(SUCC_LINK(ptr))), 0);
		}
		PUT(root, GET(SUCC_LINK(ptr)));
	}
	else{
		if(GET(SUCC_LINK(ptr)) != NULL){
			PUT(PRED_LINK(GET(SUCC_LINK(ptr))), GET(PRED_LINK(ptr)));
		}
		PUT(SUCC_LINK(GET(PRED_LINK(ptr))), GET(SUCC_LINK(ptr)));
	}
	PUT(SUCC_LINK(ptr), 0);
	PUT(PRED_LINK(ptr), 0);
}

static void *find_fit(size_t asize){ //first -fit.
    char *addr = GET(root);
    while(addr != NULL){
        if(GET_SIZE(HDRP(addr)) >= asize){
        	return addr;
		}
        addr = GET(SUCC_LINK(addr));
    }
    return NULL;
}

static void place(void *bp,size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    normalize(bp);
    
	if((csize - asize) >= (2 * DSIZE)){ // split the block.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); 
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0)); //change header & footer. 
        PUT(SUCC_LINK(bp), 0);
        PUT(PRED_LINK(bp), 0); //reset links.
        coalesce(bp); // coalesce.
    }
    else{ // enough space remains: do not split.
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

int mm_check(void){
    
}
