Formal Verification: Tree Sort
=======

“The best programs are written so that computing machines can perform them quickly and so that human
beings can understand them clearly.”

─Donald Knuth

## The algorithm

A tree sort is a sort algorithm that builds a binary search tree from the elements to be sorted,
and then traverses the tree (in-order) so that the elements come out in sorted order. Its typical 
use is sorting elements online: after each insertion, the set of elements seen so far is available 
in sorted order. (See [Wikipedia](https://en.wikipedia.org/wiki/Tree_sort)).

---

## Coq

I used CoqIde 8.6. The script contains:

    * Definitions: binary tree, binary search tree, tree sort, etc.
    * Functions: in-order transversal, list-to-BST, etc.
    * Formalized proof of the tree sort correctness.
