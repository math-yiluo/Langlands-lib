# Geometry of actual semigroup intersections

This derived supporting unit works with group schemes over an arbitrary field
`k : Type u`, actual automorphic split-torus actions, and subgroup functors on
all test schemes. It proves the smoothness and Lie-image steps needed for
semigroup intersection comparison. The semigroup-specific geometric results
retain the full `SemigroupRealizationStatement` as an explicit premise.

`SubgroupFunctor.IsRepresentedBy.comap_subgroupIntersectionFst` identifies the
actual inverse-image functor with the first projection of the scheme-theoretic
pullback of a closed subgroup representative. The proof uses the pullback
universal property on every test scheme, so it concerns the entire subgroup
functor and not just rational points.

`fullLie_homOfLe_of_hasLieImage` applies to included represented subgroups with
the same actual tangent image. A dual-number point of the larger representative
maps into the common ambient Lie image and therefore lifts to the smaller
representative. Monicity of its ambient inclusion shows that the lift reduces
to the identity. Monicity of the larger inclusion proves the required equality
after the induced homomorphism between representatives. This is the actual
identity-kernel lifting argument of `RepresentedLieUniqueness`, with no
smoothness or connectedness hypothesis in this lifting step.

`identityComponentIsoOfLeOfHasLieImage` constructs an isomorphism from a smooth
connected smaller representative to the identity component of a smooth,
affine, locally finite-type larger representative, when both inclusions in the
same affine ambient group are closed and their Lie images agree. The induced
closed inclusion has full Lie algebra by the preceding lifting argument. The
published `isOpenImmersion_of_fullLie` makes it open, and
`IdentityComponent.isoOfIsOpenImmersion` then constructs the isomorphism. The
`identityComponentIsoOfLeOfHasLieImage_fac` theorem states compatibility with
the two original ambient inclusions. No connectedness of the larger
representative is assumed.

For an equivariant closed inclusion `j : H → G`, equivariance preserves
stability under inverse image. A nonzero tangent weight of the inverse image
of `G_A` maps injectively to a nonzero tangent weight in `G_A`. The exact ambient
Lie image and independence of split-torus weight spaces force that weight to
lie in `A`. For an affine locally finite-type representative of this inverse
image, the torus weight decomposition then puts its entire tangent image in
the selected weight span of `H`. The reverse containment follows from
closed-inclusion semigroup functoriality and the exact internal Lie image.
This proves `hasLieImage_comap_semigroup`; its finite-type hypotheses on `G`,
`H`, and the representative are explicit.

`smooth_semigroup_comap_representative` assumes that `G` and `H` are smooth and
affine and that semigroup realization holds. Any closed representative of the
inverse image is then affine and locally finite type. A smooth closed
representative of `H_A` includes in it with full Lie algebra by the preceding
comparison. The published `smooth_of_fullLie_closed_subgroup` therefore makes
the inverse-image representative smooth, without assuming it connected.
`isSmoothClosed_semigroup_comap` supplies such a representative by the actual
pullback construction. Neither theorem requires `H` connected.

Finally, `semigroup_comap_eq_of_connected` adds connectedness of a closed
inverse-image representative and proves the exact equality with `H_A` on all
tests. It applies the published uniqueness theorem for included smooth
connected closed subgroup functors with the same actual Lie image. Proving
connectedness under each of the three alternatives in
`SemigroupIntersectionStatement` remains separate work; this unit proves none
of those alternatives and does not prove the host comparison conjunction.
