# Moving an original occurrence to the front

Worker 320's internal proposition `Langlands.Combinatorics.MoveOccurrenceToFront`
describes finite transport by adjacent swaps. A permutation of `Fin r` sends a
new position to its original label. The supplied predicate `P` holds for the
identity permutation. Whenever the original labels currently at adjacent
positions satisfy the supplied relation `R`, the adjacent swap preserves `P`.

For a specified original label `i`, assume `R j i` for every original predecessor
`j < i`. The conclusion is `P (Fin.cycleRange i).symm`. This permutation sends
new position zero to original label `i`, shifts the earlier labels one position
to the right in their original order, and fixes every later label.
If `r = 0`, the final universal quantifier has no instances. If `i = 0`, the
conclusion follows from the identity case.

This is a proposed elementary consequence of successively swapping the chosen
occurrence leftwards. At each step its left neighbour is the next original
predecessor. It requires no symmetry, transitivity or irreflexivity of `R`.
Original labels keep repeated values distinct.

The intended representation-theoretic use takes `P` to express an actual
induction isomorphism or a retained induction embedding, and `R` to express an
available commutation of two original factors. This proposition supplies only
finite transport: it assumes the adjacent preservation implication and supplies
no representation-theoretic commutation or classification result. Its
provenance is internal; it is not attributed to an external source.
