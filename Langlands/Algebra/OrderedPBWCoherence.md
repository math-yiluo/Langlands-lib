# Coherence of ordered Lie-word reductions

Author: Worker 1687. This internal proof uses the concrete reductions from
`OrderedPBWReduction`, with no external diamond lemma or PBW hypothesis.

`RespectsBelow b w f` expresses that a linear endomorphism `f` of the free word
module respects every reduction with left-hand word strictly below `w`.
First, whenever a two-letter word and its reversed word have shorter length
than `w`, the head reduction, skew symmetry and the alternating identity
`⁅x,x⁆ = 0` imply the expected commutator identity under `f`. Expanding one
argument in the supplied basis extends it to insertion of any Lie element.
The proof does not divide by two and remains valid in characteristic two.

`head_disjoint` treats a head inversion and a reduction later in the tail.
It reduces the swapped word in its tail, reduces each bracket-coordinate word
in its tail, and reduces the head of each word in the tail's right-hand side.
Triangularity places each required relation strictly below the original word;
linearity then makes the two resulting expressions equal.

`head_overlap` treats `i > j > h` followed by any tail. Four smaller-word
reductions take the two initial choices to the same ascending permutation of
the triple, leaving three pairs of bracket corrections. The shorter-word
commutator identity changes each correction pair to its nested bracket. Their
remaining sum is

`[[j,h],i] - [[i,h],j] + [[i,j],h]`,

which vanishes by the Lie Jacobi identity in its `lie_lie` form and skew
symmetry. All these brackets mean the brackets of the corresponding basis
vectors. Additive-group normalization finishes the equality.

Finally `head_cons` packages the disjoint and overlap cases. Induction over
the first reduction proves `reduction_coherent`: equal head choices agree;
a head and a later choice use the packaged result; two prefixed choices apply
the induction hypothesis to `f` composed with the prepend map. Preservation
of shortlex under prepend supplies exactly the required smaller-word premise.
This proves the explicit coherence hypothesis of the generic normalizer.
