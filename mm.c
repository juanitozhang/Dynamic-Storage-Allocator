/* 
 * Simple allocator based on implicit free lists, first fit search,
 * and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      64                  4  3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  0  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is 1 
 * if and only if the block is allocated. The list has the following form:
 *
 * begin                                                             end
 * heap                                                             heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(16:a) | ftr(16:a) | zero or more usr blks | hdr(0:a) |
 *  -----------------------------------------------------------------
 *          |       prologue        |                       | epilogue |
 *          |         block         |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "string",
    /* First member's full name */
    "Juanito Zhang Yang",
    /* First member's email address */
    "zhangyangj@carleton.edu",
    /* Second member's full name (leave blank if none) */
    "Duc Nguyen",
    /* Second member's email address (leave blank if none) */
    "nguyend@carleton.edu"
};

/* Basic constants and macros */
#define WSIZE       8       /* word size (bytes) */  
#define DSIZE       16      /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    16      /* overhead of header and footer (bytes) */

/* NOTE: feel free to replace these macros with helper functions and/or 
 * add new ones that will be useful for you. Just make sure you think 
 * carefully about why these work the way they do
 */

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* Perform unscaled pointer arithmetic */
#define PADD(p, val) ((char *)(p) + (val))
#define PSUB(p, val) ((char *)(p) - (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0xf)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       (PSUB(bp, WSIZE))
#define FTRP(bp)       (PADD(bp, GET_SIZE(HDRP(bp)) - DSIZE))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  (PADD(bp, GET_SIZE(HDRP(bp))))
#define PREV_BLKP(bp)  (PSUB(bp, GET_SIZE((PSUB(bp, DSIZE)))))

/* Read and write an address at address p */
#define GET_PTR(p)       (*(void**)(p))
#define PUT_PTR(p, val)  (*(void**)(p) = (val))

/* Returns the pointer to the first char in the heap */
#define LL_START       (PSUB(heap_start, 16))

/* Global variables */

// Pointer to first block
static void *heap_start = NULL;

/* Function prototypes for internal helper routines */

static bool check_heap(int lineno);
static void print_heap();
static void print_block(void *bp);
static bool check_block(int lineno, void *bp);
static void *extend_heap(size_t size);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static size_t max(size_t x, size_t y);

static void remove_node(void *bp);
static void insert_node(void *bp);

/* Our heap implementation is a explicit free list. Each 
   block has a header and a footer of 8 bytes. It packs 
   a long unsigned integer representing the size and the 
   allocated bit. The minimum payload size is 16 bytes. The first
   byte of the heap stores a pointer to the first free block in 
   explicit list. It is followed by an allocated block of size 0 
   payload. At the end of the heap it has one single header of an
   allocated block of size 0. The free blocks store in the first
   byte of the payload a pointer to the previous free block. Similarly
   the next 8 bytes store a pointer to the next block. If the block
   is the first in the free list then prev = NULL. If it is the last
   then next = NULL. We store recently created free blocks first in the
   explicit list. We find the first free block that is big enough 
   by iterating from the front of the list. We split the free block
   if the remianing free block would have size of at least 32 bytes. 
   We coalesce as soon as we introduce new free blocks. 
   
*/

void remove_node(void *bp) {
    /* Removes the block pointed by bp from our abstraction
    of the explicit free list. Since it is the a doubly linked
    list we just need to manipulate the pointers of the blocks
    around *bp
    */
    if(GET_PTR(LL_START)==NULL){ //If there is nothing in the list
        return;  //Do nothing
    }
    if(bp == NULL){ //If the block is null
        return; //Do nothing
    }
    
    void* pblkp = GET_PTR(bp); //The pointer to the prev node
    void* nblkp = GET_PTR(PADD(bp,8)); //pointer to next node

    if( pblkp == NULL && nblkp == NULL){ //First and only node.
        PUT_PTR(LL_START, NULL);  
    }
    else if(nblkp == NULL){ //Last node. 
        PUT_PTR(PADD(pblkp, 8), NULL); //The address corresponds to 
    }                                   //where next is stored in prev node
    else if (pblkp == NULL){ //First node, with something behind. 
        PUT_PTR(LL_START, nblkp);
        PUT_PTR(nblkp, NULL); 
    }
    else{ //Middle node. 
        PUT_PTR(nblkp, pblkp);
        PUT_PTR(PADD(pblkp, 8), nblkp);
    }
    
}

void insert_node(void *bp) {
    /* Creates and inserts a new node with address bp into the 
    beginning of our explicit free list.
    */
    void* head = GET_PTR(LL_START); //the first node in the list

    if (head != NULL){
        PUT_PTR(head, bp); //If there is nothing simply insert
    }
    //creating the node
    PUT_PTR(bp, NULL); //there is nothing before
    PUT_PTR(PADD(bp, 8), head); //the next pointer points to the old first node.
    PUT_PTR(LL_START, bp); //the start of the list changed. 
}
/* 
 * mm_init -- Initializes the heap: 
 * first byte stores a pointer to null (initialization of explicit free list)
 * prologue block and epilogue blocks also created. 
 * heap_start points to the payload of epilogue block
 */
int mm_init(void) {
    /* create the initial empty heap */
    if ((heap_start = mem_sbrk(4 * WSIZE)) == NULL)
        return -1;
    
    PUT_PTR(heap_start, NULL);  /* alignment padding, linked list initiliazition */
    PUT(PADD(heap_start, WSIZE), PACK(OVERHEAD, 1));  /* prologue header */
    PUT(PADD(heap_start, DSIZE), PACK(OVERHEAD, 1));  /* prologue footer */
    PUT(PADD(heap_start, WSIZE + DSIZE), PACK(0, 1));   /* epilogue header */
    
    heap_start = PADD(heap_start, DSIZE); /* start the heap at the (size 0) payload of the prologue block */
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    
    return 0;
}

/* 
 * mm_malloc -- Allocates a memory chunk of chosen input size
 * argument: unsigned long int size. 
 * returns a pointer to the start of the newly allocated block
 */
void *mm_malloc(size_t size) {
    
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      
    
    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;
    } else {
        /* Add overhead and then round up to nearest multiple of double-word alignment */
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);
    }
    /* Search the free list for a fit */

    if ((bp = find_fit(asize)) != NULL) {

        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = max(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

/* 
 * mm_free -- Frees a previously allocated block,
 * the argument is a pointer to the start of the block
 * that was previous allocated and that we want to free
 * Apart from freeing the the block, it also adds a new
 * node to the explicit free list and coalesces on bp. 
 */
void mm_free(void *bp) {

    void *headp = HDRP(bp); //header pointer of block to be freed
    void *footp = FTRP(bp); //footer
    
    PUT(headp, PACK(GET_SIZE(headp),0)); //Pack the same size, but with
    PUT(footp, PACK(GET_SIZE(footp),0)); //a allocation bit set to zero. 
    insert_node(bp);
    coalesce(bp);
}

/*
 * mm_realloc -- This function realloc a new block size
 * for a block that is already in the heap
 * The function take in the original pointer and the new size
 * The function would return the pointer to the new position of the block
 * If the pointer is null, we mallocate the necessary size
 * If the size is zero, we free the block with the pointer
 * If the size is larger than zero, we free the old block
 * Then, we copy only the necessary information depend on the relation
 * between the new block size and the old one to the newly mallocated block
*/
void *mm_realloc(void *bp, size_t size) {
   
    //cast the pointer to string to copy the data to new pointer
    char *old_ptr = bp;
   
    if (bp == NULL) {
        return mm_malloc(size);
    } else if (size == 0) {
        mm_free(bp);
        return NULL;
    } else {
        size_t old = GET_SIZE(HDRP(bp)); // get the old block size
       
        // If the new size is smaller than old size, copy only part smaller than size
        if (size <= old) {
            old = size;
        }
       
        //mallocate the new block
        char *ptr = mm_malloc(size);
       
        //copy the data form the old block to the new block
        for (size_t i = 0; i < old; i++) {
           ptr[i] = old_ptr[i];
        }
       
        //free the old block
        mm_free(bp);
        return ptr;
    }
    return NULL;
}


/* The remaining routines are internal helper routines */


/* 
 * place -- Place block of asize bytes at start of free block bp 
 *          and split the remaining memory space into a free block
 *          if it has least 32 bytes. 
 * Takes a pointer to a free block and the size of block to place inside it
 * Returns nothing
 */
static void place(void *bp, size_t asize) {

    size_t remaining =  GET_SIZE(HDRP(bp))- asize;//Internal fragmentation. 
                    //The remainder space if we were to allocate the whole block
    if (remaining < 2 * OVERHEAD) { //If the remainder is too small, 
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1)); //Simply allocate the whole block
        PUT(FTRP(bp), PACK(GET_SIZE(FTRP(bp)), 1));

        remove_node(bp); //Remove from explicit list. 
        
    } else { //There is the possibility of splitting
    PUT(HDRP(bp), PACK(asize, 1)); //allocating block
    PUT(PADD(bp, asize - (OVERHEAD)), PACK(asize,1)); //That is the address of footer. 
    remove_node(bp); //Remove the current block.

    //This is where the the free block starts
    PUT(PADD(bp, asize - WSIZE), PACK(remaining, 0));
    PUT(PADD(bp, asize + remaining - (OVERHEAD)), PACK(remaining, 0));
    //The following adress corresponds to the start of the payload. 
    insert_node(PADD(bp, asize)); //Add the new free block to the free list. 
    coalesce(PADD(bp, asize));
    }
}

/*
 * coalesce -- Boundary tag coalescing. 
 * Takes a pointer to a free block
 * Return ptr to coalesced block
 * We are assuming that bp has been added to the free list. 
 */
static void *coalesce(void *bp) {
    //Error checking
    if(bp == NULL){
        return NULL;
    }
    
    void *headp = HDRP(bp); //header pointer of bp
    void *footp = FTRP(bp); //footer pointer
    
    void *prev_headp = HDRP(PREV_BLKP(bp)); //The head pointer of the prev node
    void *next_footp = FTRP(NEXT_BLKP(bp)); //The foot pointer of next node. 
                                            //If we were to coalesce we manipulate these addresses
    
    //The alloc bit of prev and next nodes
    size_t alloc_bit_prev = GET_ALLOC(prev_headp);
    size_t alloc_bit_next = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
    
    if((!alloc_bit_next) && (!alloc_bit_prev)){ //Both free
        remove_node(NEXT_BLKP(bp)); //The start of the block is in the previous block
        remove_node(bp); //So we let its header have the information and remove these blocks
        PUT(prev_headp, PACK(GET_SIZE(prev_headp) + GET_SIZE(headp) + GET_SIZE(next_footp),  0)); //The new block has the combine size of all three.
        PUT(next_footp, PACK(GET_SIZE(prev_headp),  0));
        
        return PREV_BLKP(bp); //Block starts at this address now. 
    }
    else if(!alloc_bit_prev){ //Only previous is not allocated
        remove_node(bp); //The start of the block is the previous block.
        PUT(prev_headp, PACK(GET_SIZE(prev_headp) + GET_SIZE(headp),  0));
        PUT(footp, PACK(GET_SIZE(prev_headp),  0));
        return PREV_BLKP(bp);
    }
    else if(!alloc_bit_next){ //Only next is not allocated 
        remove_node(NEXT_BLKP(bp)); //bp is the start of the block
        
        PUT(headp, PACK(GET_SIZE(headp) + GET_SIZE(next_footp),  0));
        PUT(next_footp, PACK(GET_SIZE(headp),  0));
        return bp;
    } 
    else { //Both allocated
        return bp; //Do nothing
    }
    return bp;
}


/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize) {
    /* search from the start of the free list to the end */
    void* cur_bp = GET_PTR(LL_START); //start at the start of the free list
    
    while(cur_bp != NULL){ //while we have not arrived to the end of the list,
       if (GET_SIZE(HDRP(cur_bp)) >= asize){ //If the free block has enough space
 
            return cur_bp; //return it
        }
        //The next block's address is stored in cur_bp+8. 
        cur_bp = GET_PTR(PADD(cur_bp,8));
  }
    return NULL;  /* no fit found */
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = words * WSIZE;
    if (words % 2 == 1)
        size += WSIZE;
    // printf("extending heap to %zu bytes\n", mem_heapsize());
    if ((long)(bp = mem_sbrk(size)) < 0) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
    /* Coalesce if the previous block was free */
    insert_node(bp);
    return coalesce(bp);
}

/* 
 * check_heap -- Performs basic heap consistency checks for an implicit free list allocator 
 * and prints out all blocks in the heap in memory order. 
 * Checks include proper prologue and epilogue, alignment, and matching header and footer
 * Takes a line number (to give the output an identifying tag).
 */
static bool check_heap(int line) {
    char *bp;

    if ((GET_SIZE(HDRP(heap_start)) != DSIZE) || !GET_ALLOC(HDRP(heap_start))) {
        printf("(check_heap at line %d) Error: bad prologue header\n", line);
        return false;
    }

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!check_block(line, bp)) {
            return false;
        }
    }
    
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("(check_heap at line %d) Error: bad epilogue header\n", line);
        return false;
    }

    return true;
}

/*
 * check_block -- Checks a block for alignment and matching header and footer
 */
static bool check_block(int line, void *bp) {
    if ((size_t)bp % DSIZE) {
        printf("(check_heap at line %d) Error: %p is not double-word aligned\n", line, bp);
        return false;
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("(check_heap at line %d) Error: header does not match footer\n", line);
        return false;
    }
    return true;
}

/*
 * print_heap -- Prints out the current state of the implicit free list
 */
static void print_heap() {
    char *bp;

    printf("Heap (%p):\n", heap_start);

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        print_block(bp);
    }

    print_block(bp);    
}

/*
 * print_block -- Prints out the current state of a block
 */
static void print_block(void *bp) {
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: End of free list\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
       hsize, (halloc ? 'a' : 'f'), 
       fsize, (falloc ? 'a' : 'f')); 
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}
