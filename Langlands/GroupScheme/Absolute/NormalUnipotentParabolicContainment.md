# Normal unipotent subgroups in geometric parabolics

This internal composition extends the published algebraically closed field
normal-unipotent Borel containment theorem to geometric parabolic subgroups
over any field. It applies in arbitrary universe `u` and both characteristics.

`NormalUnipotentParabolicContainmentStatement` asserts the following. Let `G`
be a smooth connected affine group over a field `k`. Let `i : U → G` be a
closed subgroup with `U` smooth, connected and unipotent, whose represented
subgroup functor is normal. For every geometric parabolic `p : P → G`, the
full subgroup functor `range i` is contained in `range p`. This is containment
on every relative scheme test, with no rational-point restriction. The ambient
group need not be reductive, and the field need not be perfect.

The theorem `IsParabolicSubgroup.normalUnipotent_le` implements this result.
Base change to the actual algebraic closure preserves closedness, smoothness,
connectedness, unipotence and normality of the supplied subgroup. The published
`normalUnipotentBorelContainment` places its base change inside the Borel
subgroup furnished by the definition of `IsParabolicSubgroup`. That Borel's
factorization through the base-changed parabolic gives containment in the
parabolic. Finally, `SubgroupFunctor.le_range_of_baseChange_le` reflects this
containment along the faithfully flat quasi-compact algebraic-closure map,
using the parabolic's closed immersion as a represented monomorphism.

The represented-radical specialization is the existing
`IsParabolicSubgroup.radical_le` from
[`Reductive.ParabolicUnipotentKernel`](../Reductive/ParabolicUnipotentKernel.md).
It applies to any represented unipotent radical `IsUnipotentRadical i` of `G`.
`normalUnipotentParabolicContainment` proves the displayed universal Prop.

The actual published inputs are `normalUnipotentBorelContainment` from
`Absolute.NormalUnipotentBorelContainmentProof`, `IsUnipotent.baseChange` from
`Unipotent.BaseChange`, `connectedSpace_baseChange_of_smooth_affine` from
`GeometricConnectedness`, `IsClosedSubgroup.baseChange`, `range_baseChangeHom`
and `IsNormal.baseChange` from `SubgroupBaseChange`,
`le_range_of_baseChange_le` from `SubgroupFunctor.FpqcDescent`, and
`fieldExtension_fpqc` from `BaseChangeReflection`. The parabolic predicate is
the existing `Absolute.Borel.IsParabolicSubgroup`; the reused radical theorem uses
`IsUnipotentRadical` from `Reductive.UnipotentRadical`. No new mathematical
predicate is substituted for that geometric parabolic notion.

This unit provides a necessary input for correspondence of geometric
parabolics through unipotent quotients. It constructs no quotient, integral
model, building facet correspondence or prescribed-point apartment. The host
`UnramifiedFixedPointSplitTorusStatement` remains open.
