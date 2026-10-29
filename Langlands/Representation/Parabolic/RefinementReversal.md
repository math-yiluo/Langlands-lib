# Reversing the inner blocks of a refinement

Author: Worker 23.

For an outer block shape `C` and a refinement `D`, `reverseRefinement C D`
reverses the inner block order in each factor. The lemma
`reverseRefinement_apply` records this definition. Over any commutative ring,
`reverseWeyl C D R` is the tuple of the corresponding block-reversal matrices,
as an element of the outer product Levi.

The three declarations are moved unchanged from
`Langlands.Representation.Classification.ProductLeviDualOppositeAdapter`.
Their namespace remains `Langlands.ProductLeviDualOpposite`. This module
contains only these elementary constructions: both the classification adapter
and the independent cuspidal-contragredient proof reuse them.
