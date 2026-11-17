# Coefficient-test naturality of actual simple pinning points

Worker 591. This internal adapter proves the coefficient naturality needed
to extend affine pinned comparisons to all affine tests over an arbitrary
common scheme. It is derived from the published actual dual-number kernels,
coefficient maps and pinning-point constructions.

`dualCoefficientMap` sends an actual coefficient-spectrum map `Spec B → Spec A`
to its dual-number coefficient map `Spec B[ε] → Spec A[ε]`. It is defined
using the underlying ring homomorphism, so it does not depend on the choice
of original model ring. Its base identity is the ordinary naturality of
the inclusion of constants into dual numbers.

For an affine pinned model pulled to any scheme, take an affine test
`Spec A` and a refinement `Spec B → Spec A`, both with the original model
algebra structures compatible with their actual maps to the common scheme.
`rootVectorPoint_coefficient` proves that precomposing the actual simple
pinning point on `A[ε]` with the dual coefficient map is exactly the pinning
point on `B[ε]`.

The proof recovers the original-base algebra homomorphism `A → B` from the
actual map of affine tests by full faithfulness of relative `Spec`. Its
underlying ring map is the preimage of the coefficient-spectrum morphism.
Composition of the actual Lie-kernel coefficient maps then carries the
original pinning vector at `A` to that at `B`. Comparing the two projections
of the actual group pullback proves equality of the complete pinning-point
maps. No field, locality, reducedness or nonempty-base hypothesis is used.
