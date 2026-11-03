# Smooth closed subgroup comparison on algebraically closed field points

This internal derived unit upgrades comparisons on rational points to comparisons
on every test scheme. It composes the published containment criterion
`SubgroupFunctor.range_le_iff_algClosed_points`, smooth reducedness, and the
constructed smooth closed representative of the actual dynamic parabolic. It
does not prove the geometric classification of parabolics by cocharacters.

Fix an algebraically closed field `k : Type u` and a group scheme `G` over `k`.
For represented subgroup functors `F` and `F'`, if the representative of `F` is
smooth and the inclusion representing `F'` is closed, then
`IsRepresentedBy.le_iff_algClosed_points_of_smooth` identifies `F ≤ F'` with
containment of their subgroups of `G(k)`. Neither smoothness of the target nor
closedness of the source is required by this containment lemma. The proof uses
`SmoothReducedProof.isReduced_of_smooth_over_field`; smoothness also supplies
local finite type. It then rewrites both represented functors as ranges and
applies the existing reduced-source containment criterion.

Applying this lemma in both directions proves
`IsRepresentedBy.eq_iff_algClosed_points_of_smooth` for smooth closed
representatives. The definition
`SubgroupFunctor.smoothClosedSubgroupPointsOrderEmbedding` packages the result
as an order embedding from the subtype of subgroup functors with a smooth closed
representative to subgroups of `G(k)`. Its value is the original functor's
subgroup at `Spec k`. No representative is selected and no connectedness,
affineness or reductivity assumption on `G` is made for this order embedding.

For the dynamic specializations, assume that `G` is affine and let
`χ` be any actual cocharacter of `G`. The theorem
`Dynamic.le_parabolic_iff_algClosed_points` compares a smooth represented
subgroup with `Dynamic.parabolic χ`, using
`Dynamic.Affine.isRepresentedBy_parabolicHom` and
`Dynamic.Affine.isClosedSubgroup_parabolicHom`. For the reverse containment,
assume also that `G` is smooth.
`Dynamic.parabolic_le_iff_algClosed_points` obtains smoothness of that same
representative from the proved theorem `dynamicSmooth`. The other subgroup
needs a closed representing inclusion for this reverse implication.

Finally, for smooth affine `G`,
`Dynamic.range_eq_parabolic_iff_algClosed_points` states that for any smooth
group scheme `H` with a closed inclusion `i : H ⟶ G`, the equality
`SubgroupFunctor.range i = Dynamic.parabolic χ` holds if and only if the two
subgroups at `Spec k` are equal. Both sides retain the original ambient group,
homomorphism and cocharacter. The conclusion is equality of the functors on all
test schemes, including nonaffine and nonreduced tests. The proof introduces
the range representation of the closed inclusion and combines the two proved
containment implications.

All statements retain algebraic closedness of `k`. They neither descend a
cocharacter to another field nor establish equality of rational points for a
given parabolic. Those are separate structural obligations in the fixed-torus
classification.
