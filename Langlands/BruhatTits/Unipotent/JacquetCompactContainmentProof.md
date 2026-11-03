# The S22 adapter to Jacquet compact-subgroup containment

`Langlands.BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups` proves the
published proposition
`Langlands.BruhatTits.DynamicUnipotentIsLimitOfCompactSubgroupsStatement.{u}`
at an arbitrary universe `u`.

The theorem assumes
`Langlands.BruhatTits.DynamicUnipotentCompactOpenContainmentStatement.{u}`.
For every nonarchimedean local field `F : Type u`, actual group scheme `G`
over `Spec F`, explicit `hG : Langlands.GroupScheme.IsConnectedReductive G`,
and rational cocharacter `χ`, it concludes that the actual subgroup

```text
U := (Langlands.GroupScheme.Dynamic.unipotent χ).carrier
  (Over.mk (𝟙 (Spec (CommRingCat.of F))))
```

satisfies `Langlands.Jacquet.Localization.IsLimitOfCompactSubgroups` with
the inherited canonical rational-point topology. The field instances and
all other quantifiers are exactly those of the published proposition.

The proof first introduces the S22 hypothesis and the field, group and
cocharacter telescope. It then explicitly re-installs the statement's
three local instance bindings in the same order: `hG.isAffineHom` as
`IsAffineHom G.X.hom`, `isAffine_of_isAffineHom G.X.hom` as
`IsAffine G.X.left`, and
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X`
as the topology on the identity-test point group
`Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X`.
These bindings in the proposition are inlined, so introducing its
quantifiers alone does not install them in the proof's local context.
Re-installing them makes the S22 application use precisely the topology
on the goal's ambient group and its inherited topology on `U`.

For an arbitrary compact set `C : Set U`, the hypothesis applied at the
same `F`, `G`, `hG`, `χ`, `C` and compactness proof produces
`K : OpenSubgroup U`, compactness of its carrier, and `C ⊆ K`.
The proof returns `K.toSubgroup`. Its carrier is definitionally the same
set as that of `K`, so the compactness proof and containment proof transfer
unchanged. This supplies the existential subgroup required by
`IsLimitOfCompactSubgroups`.

This is an elementary derived adapter between the two published
propositions, following the proof route supplied by Worker 1236. The
source provenance of the structural premise is recorded in
[the target statement's documentation](JacquetCompactContainmentStatement.md).
The present proof establishes the conditional implication; the structural
S22 premise, Jacquet exactness, unimodularity and the other S19–S23
obligations remain separate.

Authors: Worker 1277; Worker 1236 supplied the proof route.
