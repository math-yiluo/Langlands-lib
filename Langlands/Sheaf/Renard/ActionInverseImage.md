# Equivariant inverse image underlying Renard III.3.2 restriction

This is an internal construction needed for the restriction functor of
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, III.3.2, printed p.84 / PDF p.90. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard restricts the sheaf to a locally closed subgroup-invariant
subspace and restricts the group action. This pair constructs the
underlying inverse-image sheaf for every continuous equivariant map.
The smoothness required to lift it to Renard's smooth-action categories
is not asserted here.

The new declarations have prefix
`Langlands.Sheaf.Renard.SectionActions`. They operate on the published
`Langlands.Sheaf.Equivariant.TopologicalSheaf` objects specialized to
complex coefficients by `ActionSheaf`.

For a continuous equivariant map `f : X → Y`, the existing
`DirectImage.preimage f hf` sends an open of `Y` to its literal
inverse image in `X`, retaining every group label. Its direct-image
precomposition is the existing `DirectImage.sheaf`. The instance
`preimage_isContinuous` proves continuity for the existing
`transportTopology` on each space: an ordinary sheaf remains a sheaf
after this direct image, by the published `DirectImage.isSheaf`,
and the published `isSheaf_transportTopology_iff` converts between
the ordinary-open condition and the transport-site condition.
This is the site-theoretic continuity used for inverse image.

`actionInverseImage f hf` first applies the published
`sheafEquivalence` to view an equivariant sheaf as a sheaf on its
transport site. It then applies Mathlib's actual
`Functor.sheafPullbackConstruction.sheafPullback`: forget to
presheaves, take left Kan extension along the opposite of
`DirectImage.preimage f hf`, and sheafify on the target transport
site. Finally it applies the inverse of the published
`sheafEquivalence`. No inverse-image functor or comparison
equivalence is supplied as a hypothesis.

`actionSiteAdjunction` is the intrinsic site-level adjunction of
that Kan-extension/sheafification construction with direct-image
precomposition. It is obtained from Mathlib's constructed
`sheafAdjunctionContinuous`. It records the universal-property
meaning of the inverse image; it asserts no smoothness or
compact-section comparison. `actionInverseImageAdjunction` composes
this adjunction with the two published equivalences. Its right
adjoint is definitionally the existing literal `DirectImage.sheaf`,
so the universal property holds on the original action-sheaf
categories as well.

`subgroupSpaceRestriction Q i hi` first applies the actual
`subgroupRestriction Q` from `StalkActions`, retaining the
ordinary sheaf and restricting the group labels. It then applies
the constructed `actionInverseImage` along `i : Z → Y`.
For a continuous inclusion of a locally closed `Q`-invariant
subspace, this is its underlying restriction sheaf. The construction
itself needs neither injectivity nor locally closedness of `i`,
and needs neither closedness of `Q` nor local compactness.
Those are source hypotheses for Renard's smooth restriction,
which remains a separate construction obligation.

All spaces, groups and section carriers here are in `Type`
(universe zero). This size specialization makes the transport
sites small and lets the existing complex module category supply
the colimits and sheafification. The group need not carry a
topology for inverse image itself: continuity of each individual
operator suffices for the transport sites. The subgroup-space
construction introduces the topology on `G` used by
`subgroupRestriction`. No theorem dropping Renard's joint
continuity, Hausdorff, total-disconnectedness or local-compactness
hypotheses is claimed.
