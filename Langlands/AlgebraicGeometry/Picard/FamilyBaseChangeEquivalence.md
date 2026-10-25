# Equivalence of actual rigidified families across ground base change

For a morphism `b : S' → S`, an abelian scheme `A/S`, and a scheme `T/S'`,
the existing `familyBaseChangeSpaceMap` identifies the actual spaces
`T ×_{S'} A_{S'}` and `T ×_S A`. The inverse map has projections to `T`
and to `A_{S'}` given by the projections to `A` and `T → S'`.
The pullback universal property proves that these maps are inverse.

The comparison preserves the relative unit sections. Pulling back actual
rigidified line bundles along the two inverse maps therefore gives inverse
functors. The unit and counit comparisons use the published identity and
composition coherence of canonical rigidified pullback. The resulting
`familyBaseChangeEquivalence` has the existing `familyBaseChange` as its
forward functor.

This is an internal construction derived from the published fibre products
and rigidified pullback functors. It makes no new existence assertion about
a dual scheme and no claim about the geometric Picard-zero predicate. All
schemes are arbitrary in one universe.
