/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Sentinals",
	/* First member's full name */
	"Kshitij Sharma",
	/* First member's email address */
	"201201146@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Ashish Dubey",
	/* Second member's email address (leave blank if none) */
	"201201129@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute` address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */ 
static char **free_listp1;/* Pointer to first free block */
static char **last_free_listp1;
static int extendsize=0;
static int counter1=0;
static int counter2=0;
static int size_value1;
static int size_value2;
static int w=1;


/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static int i=1;
/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* function prototype to add a pointer to the free list */
static void append_free_mem(void *bp);


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

//printf("\nIn the init.\n");
	free_listp1 = NULL;
	last_free_listp1 = NULL;
	 counter1=0;
	 counter2=0;
	 size_value1=0;
	 size_value2=0;
	 w=1;
	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);
	//printf("\n kshitijSharma");
	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	char **bp=extend_heap(CHUNKSIZE / WSIZE);	
	
	
	if (bp == NULL)
		return (-1);
		free_listp1=bp;
		//printf("kshitijSharma");
		last_free_listp1=bp;
		
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);


	//..............................trying caching..........
	
	int flag=0;
	if(w==1 && size <= 1024 && size >= 64)
	{
		if(counter1>=1)
		{
			if(size_value1==asize)
			counter1++;

		}
		else
		{	
			size_value1=asize;
			counter1++;}
			w=w*-1;
			flag=1;
		}

	if(w==-1 && flag==0 && size <= 1024 && size >= 64)
	{
		if(counter2>=1)
		{
			if(size_value1==asize)
			counter2++;
		}
		size_value2=asize;
		w=w*-1;
		counter2++;
		
	}

	if(counter1>=100 && size_value1==asize)
	{
		if((bp=mem_sbrk(asize))!=NULL)
		{	//find_fit_count=0;
			PUT(HDRP(bp), PACK(asize, 1));         // Free block header 
		    PUT(FTRP(bp), PACK(asize, 1));         // Free block footer 
			PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
		return bp;
	}
	}
	if(counter2>=100 && size_value2==asize)
	{
		if((bp=mem_sbrk(asize))!=NULL)
		{	
			PUT(HDRP(bp), PACK(asize, 1));         // Free block header 
		    PUT(FTRP(bp), PACK(asize, 1));         // Free block footer 
			PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
		return bp;}
	}




	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	
	
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	*(char **)bp=NULL;
	*((char **)bp +1)=NULL;
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */


void *
mm_realloc(void *ptr, size_t size)
{
	size_t asize, oldsize;
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	if (ptr == NULL)
		return (mm_malloc(size));
	oldsize = GET_SIZE(HDRP(ptr));
	
        if (size <= DSIZE)
                asize = 2 * DSIZE;
        else
                asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);


	if(oldsize == asize)
	{
		return ptr;
	}

	if(oldsize > asize)
	{
		return ptr;
	}

	int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
	int prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
	void *prev=PREV_BLKP(ptr);
	void *next = NEXT_BLKP(ptr);
	size_t next_size = GET_SIZE(HDRP(next));
	size_t prev_size = GET_SIZE(HDRP(prev));

	if(prev_alloc && !next_alloc && (next_size + oldsize) >= asize)
	{
		{
			if(*((char **)next + 1) != NULL)
			{
				*((char **)(*((char **)next + 1))) = *(char **)next;
			}	
			if(last_free_listp1 == (char **)next)
			{
				last_free_listp1 = (char **)(*(last_free_listp1 + 1));
				if(last_free_listp1 != NULL)
					*last_free_listp1 = NULL;
			}
			if(*(char **)next != NULL)
			{
				*((char **)(*(char **)next + WSIZE)) = *((char **)next + 1);
			}
			if(free_listp1 == (char **)next)
			{
				free_listp1 = (char **)(*free_listp1);
				if(free_listp1 != NULL)
					*(free_listp1 + 1) = NULL;
			}
			
				
		}
				memcpy(ptr, ptr, oldsize);
				PUT(HDRP(ptr), PACK(next_size + oldsize, 1));
				PUT(FTRP(ptr), PACK(next_size + oldsize, 1));
				return ptr;
	}
	//.........................................................
	if(!prev_alloc && next_alloc && (prev_size + oldsize) >= asize)
	{
		//remove_from_list(prev);
		{
			if(free_listp1 == (char **)prev)
			{
				free_listp1 = (char **)(*free_listp1);
				if(free_listp1 != NULL)
					*(free_listp1 + 1) = NULL;
			}
			if(*((char **)prev + 1) != NULL)
			{
				*((char **)(*((char **)prev + 1))) = *(char **)prev;
			}
			if(*(char **)prev != NULL)
			{
				*((char **)(*(char **)prev + WSIZE)) = *((char **)prev + 1);
			}
			if(last_free_listp1 == (char **)prev)
			{
				last_free_listp1 = (char **)(*(last_free_listp1 + 1));
				if(last_free_listp1 != NULL)	
					*last_free_listp1 = NULL;
			}
			
			
		}
		char **p1,**p2;

		int flag=0;
		void *bp = find_fit(oldsize);
		if(bp==NULL)
		{
			bp=mem_sbrk(oldsize);
			PUT(HDRP(bp), PACK(oldsize, 0));         /* Free block header */
			PUT(FTRP(bp), PACK(oldsize, 0));         /* Free block footer */
			PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
			flag=1;
		}
		else
		{	
			p1=*(char **)(bp);
			p2=*((char **)bp+1);	
		}
		memcpy(bp, ptr, oldsize);
		PUT(HDRP(prev), PACK(prev_size + oldsize, 1));
		PUT(FTRP(prev), PACK(prev_size + oldsize, 1));
		memcpy(prev, bp, oldsize);
		if(flag==1)
		{
			PUT(HDRP(bp), PACK(oldsize, 1));
			PUT(FTRP(bp), PACK(oldsize, 1));
			append_free_mem(bp);
		}
		else
		{
			*(char **)(bp)=p1;
			*((char **)bp+1)=p2;	
		}
	return prev;
	}
	
	void *newptr;
	newptr = mm_malloc(size);

	if (newptr == NULL)
		return (NULL);

	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	mm_free(ptr);

	return (newptr);
}


/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{

	int prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	char **next = (char **)NEXT_BLKP(bp);
	char **prev = (char **)PREV_BLKP(bp);


	if(prev_alloc && next_alloc) 
	{                 
		append_free_mem(bp);
		return (bp);
	}
	else if (prev_alloc && !next_alloc)
	{         
	        size_t size = GET_SIZE(HDRP(bp));
			size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
			PUT(HDRP(bp), PACK(size, 0));
			PUT(FTRP(bp), PACK(size, 0));
			*(char **)bp = *next;
			if(*next != NULL)
		{
			*((char **)(*next) + 1) = (char *)bp;
		}
       		else 
		{
       			last_free_listp1 = (char **)bp;
       		}

		*((char **)bp + 1) = *(next + 1);

		if(*((char **)bp +1) != NULL)
		{
			*(char **)(*((char **)bp + 1)) = (char *)bp;
		}
		else 
		{
			free_listp1 = (char **)bp;
		}
        
		return bp;
	} 
	else if(!prev_alloc && next_alloc)
	{       
      		
		size_t size = GET_SIZE(HDRP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		return bp;
	}
	else 
	 {                                        
	        size_t size = GET_SIZE(HDRP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		*(char **)bp = *next;
		if(*next != NULL)
		{
			*((char **)(*next) + 1) = (char *)bp;
		}
		else 
		{
			last_free_listp1 = (char **)bp;
		}
		return bp;
	}
}
/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

static void append_free_mem(void *bp)
{
	if(free_listp1==NULL || last_free_listp1==NULL)
	{
		free_listp1=(char **)bp;
		last_free_listp1=(char **)bp;
		*free_listp1=NULL;
		*(free_listp1+1)=NULL;
		
	}	
	else if(bp<(void *)free_listp1) 
	{
		*(char **)bp = (char *)free_listp1;
		*((char **)bp + 1) = NULL;
		*(free_listp1 + 1) = (char *)bp;	
		free_listp1 = (char **)bp;
	}
	else if(bp > (void *)last_free_listp1)
	{
		*last_free_listp1 = bp;
		*((char **)bp + 1) = (char *)last_free_listp1;
		*(char **)bp = NULL;
		last_free_listp1 = (char **)bp;
	}
	else
	{
		char **loop;
		char **prev = NULL, **next = NULL;
		for(loop = free_listp1 ; loop <= (void *)bp  ; )
		{
			prev = loop;
			loop = (char **)(*loop);
		}
		next = (char **)(*prev);
		*prev = (char *)bp;
		*(char **)bp = (char *)next;
		*((char **)bp + 1) = (char *)prev;
		*(next + 1) = (char *)bp;

	}
}




/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	void *bp;
	char **loop;
	
	if(free_listp1==NULL)
		return NULL;
	/* Search for the first fit. */	
	for(loop=free_listp1;loop!=NULL;)
	{
		bp=(void *)loop;
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
		{	
		return (bp);
		}
		loop = (char **)(*loop);
	}
	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 * DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		char **bp_before, **bp_after;
		bp_before = bp;
		void *bp1;
		bp1 = NEXT_BLKP(bp);
		bp_after = (char **)bp1;
		PUT(HDRP(bp1), PACK(csize - asize, 0));
		PUT(FTRP(bp1), PACK(csize - asize, 0));


		*bp_after = *bp_before;
		*(bp_after + 1) = *(bp_before + 1);

		if(*bp_after != NULL)		
			*((char **)(*bp_after) + 1) = (char *)bp_after;
		else 
			last_free_listp1 = bp_after;

		if(*(bp_after + 1) != NULL)	
		{
			*(char **)(*(bp_after + 1)) = (char *)bp_after;
		}
		else
			free_listp1 = bp_after;


	} else {


	
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));

		char **bp1 = (char **)bp;

		if(*bp1 != NULL)		
			*((char **)(*bp1) + 1) = *(bp1 + 1);
		else
                        last_free_listp1 = (char **)*(bp1 + 1);

		if(*(bp1 + 1) != NULL)	
			*((char **)(*(bp1 + 1))) = *bp1;
		else
                        free_listp1 = (char **)*bp1;
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
