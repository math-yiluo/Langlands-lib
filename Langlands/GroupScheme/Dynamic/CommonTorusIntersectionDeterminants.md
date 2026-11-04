# Actual intersection determinants on a common split torus

This internal deduction uses the published dynamic Lie theorem, equivariant
weight functoriality and the determinant root-sum theorem. All tangent and weight
spaces are the actual dual-number Lie spaces, over arbitrary fields of universe
`u`; there is no restriction on the characteristic.

The tangent image of a cocharacter centralizer is the zero-pairing region. The
tangent image of an identity-limit subgroup is the positive-pairing region.
Independence of the split torus weight decomposition identifies the intersection
of one weight space with either region. Tangent images commute with subgroup
intersection, so the two subgroup intersections have exactly the positive/zero
and positive/positive regions, with their actual ambient dimensions. These
claims require the displayed affine and locally finite type hypotheses on the
ambient group and splitness of the torus.

For any represented subgroup with such a tangent region and any action whose
restriction intertwines with ambient conjugation, the actual differential gives
the stated weight-space images and dimensions. Injectivity follows from the
representing monomorphism. The determinant root-sum formula therefore identifies
its restricted determinant character with `regionWeightCharacter`. The general
action, torus map, representability and equivariance hypotheses are explicit in
these helpers, as are finite Lie coordinates and affineness of the acting group
for the determinant formula.

`characterRestrict_determinant_unipotent_inf_centralizer` and
`characterRestrict_determinant_unipotent_inf_unipotent` specialize this argument
to the actual intersections. They identify the restricted determinant characters
with the positive/zero and positive/positive regions respectively. Neither lemma
assumes that an arbitrary supplied action is conjugation: its restriction must
satisfy the displayed actual equivariance equation.

`Dynamic.unipotentIntersectionTorusAction` and
`Dynamic.unipotentCentralizerIntersectionTorusAction` are the restrictions of
actual ambient torus conjugation to the represented unipotent/unipotent and
unipotent/centralizer intersections. Their construction works over any base
scheme, with representability explicit. The accompanying equivariance lemmas
state that the representing inclusion intertwines these actions on every test
scheme. The two `determinantCharacter` lemmas identify their determinants with
the corresponding weighted regions over the field. Those lemmas explicitly
retain affineness of the torus, which follows from splitness, and finite Lie
coordinates on the represented intersection.

The proof bodies use `dynamicLie`,
`RelativeRoot.tangentSubmodule_unipotent_eq_semigroupWeightSpan`,
`weightSpace_cocharacter_eq_iSup`, `weightSpace_disjoint_iSup`,
`RelativeRoot.tangentSubmodule_inf`,
`AutomorphicAction.IsEquivariant.map_actionWeightSpace_eq_inf_range`,
`Lie.targetMapLinear_injective`,
`AutomorphicAction.determinantCharacter_restrict_eq_rootSum` and
`AutomorphicAction.onRepresentedSubgroup_act_comp`. This is an internal
consequence of these actual-object constructions; no external literature is
needed for an additional mathematical assertion. The imported
`CommonTorusDeterminantBalance` supplies the definition of the weighted region;
its balance theorem is not used in these proof bodies.

No whole-Levi character detection, Haar-modulus comparison, geometric filtration
or exact-K0 expansion is asserted here. The proof bodies use no geometric lemma,
adjointness, cuspidal support, character independence or Langlands
classification. The broader imported-module closure does not supply any of
those as a proof premise for these results.
