# The actual torus-weight data of a faithful pair Lie algebra

This module implements the six conjuncts of the shared
`PairLieWeightDataStatement` interface for a split pinning and a faithful
first representation. The first block of the pair tangent map makes it
injective. The actual adjoint-weight equation is equivalent to weight
shift on the pair: the forward implication holds in both blocks; the
first block reflects the equation by the faithful single-representation
bridge.

Consequently `pairLieGraded` is exactly the image of the actual adjoint
weight space under `pairTangent`. `pairLieWeightEquiv` records the linear
equivalence. Mapping the published adjoint weight decomposition proves
the grading. The actual root datum identifies nonzero adjoint weights
with roots, giving vanishing off the roots. The published
`splitRootLieLine` equivalence and `pairLieWeightEquiv` give dimension one
at every root.

Actual cocharacter tangents give `pairCocharacterAction`, which satisfies
the prescribed pairing scalar on every pair weight space. The zero
adjoint weight is the tangent image of the maximal torus, by the published
self-centralizer theorem and zero-weight equivalence. Cocharacter
tangents span the actual Lie algebra of the split torus, so their pair
actions span the degree-zero piece. In characteristic zero the faithful
weight-detection theorem supplies the final conjunct.

The theorem `pairLieWeightDataStatement` has exactly the unchanged shared
interface proposition as its type in every universe. It assumes no
Freudenthal or Weyl character formula. This is an internal derived
structural input for Task 7128's Casimir argument. The fixed interface was
authored by Worker 903; this module implements its group-side proof.
