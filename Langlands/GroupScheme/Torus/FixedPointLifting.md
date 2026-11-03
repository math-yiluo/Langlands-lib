# Nilpotent lifting of diagonalizable fixed points

This internal consequence of `CharacterActionGrading` and `AffineSchemeAction`
packages their formal smoothness result as a point-lifting theorem. It works over
any commutative base ring, for any additive commutative character group in the
same universe. The ambient affine coordinate algebra is assumed formally smooth.
It does not assert normalizer representability or geometric smoothness.

`CharacterAction.exists_fixed_lift` starts with an algebra-valued point over
`C/I`, where `I` is nilpotent, that is fixed after every algebra refinement. The
fixed-ideal kernel criterion factors this point through the fixed coordinate
quotient. That quotient is formally smooth by
`CharacterAction.formallySmooth_fixedQuotient`. Mathlib's nilpotent-ideal lifting
theorem lifts the factorization to `C`. Composing with the quotient map from the
original coordinate algebra gives a lift killing the fixed ideal; the same kernel
criterion proves its fixedness after every algebra refinement.

`CharacterAction.fixedLift` chooses such a lift noncomputably. Its specifications
`fixedLift_isFixed` and `fixedLift_comp_quotient` assert fixedness after every
algebra refinement and recovery of the original point under reduction modulo
`I`. The choice uses the existence theorem and adds no uniqueness claim.

`PointwiseSchemeAction.exists_fixed_lift` transports this result through the actual affine
coordinate point equivalence for a diagonalizable group acting on an affine group
scheme as a scheme. It imposes no preservation of the target group law. The
comparison in `AffineSchemeAction` ensures fixedness after every scheme refinement,
including non-affine refinements, in both the input and the lifted point. The
reduction of the lifted point is the original point as an actual scheme morphism.

The provenance is the imported internally derived fixed-quotient proof, followed
by Mathlib's `Algebra.FormallySmooth.exists_lift` and the published affine point
comparison. No additional literature result is used here. The imported graded
square-zero argument was generalized from Worker 1131's rank-one construction.
