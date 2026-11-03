# Lifting actual Lie-kernel points along smooth affine homomorphisms

This is an internal construction derived from Mathlib's infinitesimal lifting
property for formally smooth algebras and the Library's affine coordinate
description of group schemes. It supplies the differential-surjectivity input
for equivariant smooth quotient comparisons.

Let `f : H ⟶ G` be a homomorphism of affine group schemes over a commutative ring
`R`. If its actual underlying scheme morphism is smooth, then
`targetMap_surjective_of_smooth` proves that the induced map on dual-number
identity kernels is surjective for every commutative `R`-algebra `A` in the same
universe. Neither a field assumption nor surjectivity of the original scheme
morphism is required. The definition `smoothKernelLift` chooses a preimage of
each such kernel point; `targetMap_smoothKernelLift` proves its defining
equation. This choice is a function, with no asserted linearity or naturality.
The induced differential `targetMapLinear` is surjective by
`targetMapLinear_surjective_of_smooth`.

The proof first transfers scheme smoothness across the chosen affine coordinate
isomorphisms to smoothness of the coordinate restriction ring homomorphism.
For a target kernel point, its coordinate homomorphism has constant part equal
to the target augmentation. The two augmentations commute with restriction.
The algebraic lemma `exists_dualNumberLift_of_formallySmooth` therefore lifts
the source augmentation through the first projection `A[ε] → A`, while keeping
the target dual-number point fixed. Its kernel has square zero, so Mathlib's
`Algebra.FormallySmooth.liftOfSurjective` applies after installing the
appropriate algebra structures. Translating the resulting coordinate map back
to the source gives the desired kernel point.

This unit proves differential surjectivity from scheme smoothness. A converse
criterion, smoothness or connectedness of semigroup representatives, and
surjectivity of induced semigroup scheme morphisms remain separate obligations.
