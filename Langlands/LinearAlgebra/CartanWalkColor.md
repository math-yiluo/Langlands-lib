# Cartan invariants from adjacency walk counts

This internal finite construction defines `step M c` by summing the natural
number colors `c j` over entries `M i j = -1`.

An entry-preserving bijection preserves this refinement whenever it preserves
the original colors. The proof reindexes the finite sum by that bijection,
then uses Cartan entry preservation and color preservation term by term.

Starting from the constant color one, successive refinements count walks of
each length in the graph defined by entries equal to minus one. This is used
to distinguish vertices without enumerating all vertex permutations. No
root-system classification or external source is used.
