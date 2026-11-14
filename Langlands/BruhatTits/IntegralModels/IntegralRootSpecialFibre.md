# Actual special fibres and Lie images of integral root models

This internal construction applies to a smooth affine integral model `N`
over a local domain `R`, with specified fraction field `K` and supplied
`A : IntegralSplitTorusData N i`. No building or reductivity hypothesis
is required.

`specialFibreTorus` and `specialFibreInclusion` are the actual residue
base changes of `A.torus` and `A.inclusion`. The torus stays split.
`characterSpecialization` identifies the characters of the specified
generic torus with the characters of this same special fibre. It uses
the given generic torus isomorphism and the two actual split-torus
character base-change equivalences. Its value at `a` is precisely the
residue base change of `A.integralCharacter a`.

For every nonzero generic character `a`, the actual inclusion
`(A.rootModelMap a ha).specialFibreMap` represents
`RelativeRoot.subgroup A.specialFibreInclusion
(A.characterSpecialization a)` on every test scheme over the residue
field, and is a closed subgroup inclusion. This follows from
`IntegralModel.SplitRoot.integral_properties`, the published base-change
theorem for the intrinsic root functor, and base change of subgroup
representations and closed immersions.

The actual differential range of this inclusion equals the ambient
positive cyclic weight span

```
sum of the weight spaces of n • characterSpecialization(a), n ≥ 1.
```

The Lean expression for this sum is `semigroupWeightSpan` of `cyclicTail`
at `1`. The implemented proof first identifies the differential range
with the intrinsic tangent submodule of the represented root functor,
then applies `RelativeRoot.tangentSubmodule_subgroup`. The specialized
character is nonzero because specialization is an additive equivalence.
Smoothness and affineness of the ambient special fibre follow by base
change from `N`.

`rootSpecialFibreLieEquiv` is the resulting linear equivalence from the
Lie algebra of the actual root-model special fibre to that weight span.
Its underlying map is the differential of the actual special-fibre
inclusion, as recorded by `rootSpecialFibreLieEquiv_apply_coe`; injectivity
follows from the monomorphic all-test representation.

All declarations are at arbitrary universe `u`. This is an internal
consequence of the published constructions and theorems in
`IntegralRootFiltration`, `IntegralModel.SplitRoot`,
`Rational.RootSubgroupBaseChange`, `Rational.RootSubgroupLieImage`, and
`Torus.SplitLatticeBaseChange`. It does not identify the image in a
reductive quotient, prove smoothness of the kernel of a map to that
quotient, select surviving quotient roots, or establish facet signs.
