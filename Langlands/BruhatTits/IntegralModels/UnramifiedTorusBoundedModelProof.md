# Smooth models of the maximal bounded unramified torus subgroup

`Langlands.BruhatTits.IntegralModels.unramifiedTorusBoundedModel` proves exactly
`Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelStatement.{u}`
at arbitrary universe `u`.

For every nonarchimedean local field `F : Type u`, put
`K = inertiaFixedField F` and `O = fixedFieldIntegers F`. For every actual
affine commutative group scheme `T` over `Spec K` satisfying
`IsTorus T.toGrp`, the theorem supplies an actual
`M : IntegralModel O K T.toGrp` with `M.IsSmooth` and the literal equality

```text
M.integralPoints = characterValuationKernel (fixedFieldValuation F) T.toGrp.
```

## Provenance and implemented proof

This is a derived composition of two published Library theorems:
`unramifiedTorusBoundedModelAssembly` in
[the torus reduction](UnramifiedTorusBoundedModelAssembly.md), and
`Langlands.GroupScheme.maximalBoundedIntegralModel` in
[the general model construction](../../GroupScheme/IntegralModel/MaximalBoundedConstruction.md).
The Lean proof applies the former to the latter at the same universe `u`,
discharging the reduction's sole premise.

The reduction proves that the character-valuation kernel is maximal among
algebraically bounded subgroups of the original rational-point group.
It transports this result from the integer-normalized valuation to
`fixedFieldValuation F` using equivalence of valuations. The fixed-field
arithmetic supplies that `O` is a Henselian discrete valuation ring with
algebraically closed residue field, and `IsTorus.smooth` supplies
smoothness of the generic torus.

The general theorem constructs a model of a supplied maximal bounded subgroup.
It embeds the original group into a general linear group, chooses a stable
full lattice, and constructs the ambient lattice model. The inverse image
of its integral points is algebraically bounded, so maximality identifies
it with the supplied subgroup. Schematic closure followed by smoothening
gives the smooth model, preserving the literal integral-point subgroup
through the specified generic identifications.

Finally, the reduction uses `fixedFieldIntrinsicIntegers_eq F` to transport
the general theorem from the intrinsic valuation integer ring of `K` to
the literal ring `O` in the target. Thus the final theorem retains the
target's exact model type and subgroup equality with no construction premise.

The unchanged [target statement](UnramifiedTorusBoundedModelStatement.md)
records its comparison with Kaletha–Prasad, Proposition B.7.2(2) and
Corollary B.7.4, together with the source and corrections. This theorem
asserts the stated existential smooth model and integral-point equality.
It does not assert a Néron mapping property or identify the model with a
particular standard or ft-Néron model.
