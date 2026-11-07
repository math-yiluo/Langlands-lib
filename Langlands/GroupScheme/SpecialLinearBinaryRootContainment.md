# Actual split binary images in normal subgroups containing relative roots

This internal comparison works over every field `k : Type u`, in arbitrary
characteristic. Its source is the actual split binary special linear group,
or a specified group scheme `A` with a ground-field isomorphism
`e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)`.
The target is an actual group scheme `G` over `Spec k`, and the map to `G`
is an actual group-scheme homomorphism. The subgroup `K` is an abstract normal
subgroup of the actual rational-point group `G(k)`.

The first comparison, `rationalPoints_range_le_of_upper_dynamic`, assumes
that `K` contains the rational points of the single dynamic unipotent subgroup
for `upperCocharacter ≫ f`. It concludes that the whole range of the actual
rational-point map of `f : SL₂ ⟶ G` is contained in `K`.
There is no affineness or reductivity assumption on `G` in this comparison.

Its proof takes the inverse image `K.comap (rationalPoints.map f)`, which is
normal. The explicit all-test contraction in `SpecialLinearBinaryDynamicRoots`
puts the actual upper-root image in `Dynamic.unipotent upperCocharacter`.
The existing `Dynamic.unipotent_le_comap` transports those points along `f`,
and the assumed dynamic containment therefore puts the upper-root image in
the inverse image of `K`. The normal-generation theorem
`eq_top_of_normal_upper_image` from `SpecialLinearBinaryRadicalGeneration`
makes this inverse image the whole SL₂ point group. This proves the asserted
full-image containment.

The comparison `rationalPoints_range_le_of_iso_upper_dynamic` applies the
same argument to `e.inv ≫ a`, where `a : A ⟶ G`. Every actual point of `A`
is the inverse image of its image under `e.hom`, so the conclusion is the
range containment for `a` itself.

The ambient-root comparisons retain the following explicit inputs:

- `G` is affine and connected reductive, and `i : S.toGrp ⟶ G` is an actual
  maximal split torus.
- `SmoothMaximalSplitTorusConjugacyStatement.{u}` holds.
- For every cocharacter of `S`, distinct indivisible positive roots have
  disjoint positive integral rays, expressed by the displayed `cyclicTail`
  disjointness condition.
- `K` contains the rational points of every actual relative-root subgroup
  at `i`, and `K` is normal.

Under these inputs, the existing
`dynamicUnipotent_le_normalSubgroup_of_root_groups` supplies the single
dynamic containment required above. This proves
`rationalPoints_range_le_normalSubgroup_of_root_groups` for every actual
homomorphism `SL₂ ⟶ G`, and
`rationalPoints_range_le_normalSubgroup_of_root_groups_of_iso` for a
specified actual model `A` and map `a : A ⟶ G`.

The definition `rationalPointsToNormalSubgroupOfRootGroups` restricts the
codomain of the original rational-point homomorphism to `K`, using this
proved full-image containment. Its coercion formula
`rationalPointsToNormalSubgroupOfRootGroups_apply_coe` says that its value in
`G(k)` is exactly `rationalPoints.map a x`.

The provenance is internal composition of the explicit split binary
contraction, upper-root normal generation, dynamic functoriality and the
existing ambient dynamic-containment theorem. The source isomorphism and
ambient inputs listed above remain premises. No parabolic-dynamic
presentation, centralizer-reductivity statement, source-reductivity premise,
or hypothesis about all source parabolic-radical images is needed here.
The unit does not construct presentations of general factors, prove the
retained ambient structural inputs, settle nonsplit rank-one arithmetic, or
prove the unrestricted local Kneser–Tits statement.
