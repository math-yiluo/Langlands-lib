# Compact passage from finite to absolute reciprocity images

Author: Worker 1760.

This internal derived construction associates to a subgroup of the actual
absolute Galois abelianization its `finiteAbelianSubgroupLocus`: the intersection,
over all actual finite abelian extensions in the chosen closure, of the
restriction preimages of its finite images. The base field has arbitrary
universe `u`. The equality theorem assumes that the base field is perfect and
the subgroup is closed.

The implemented proof separates a point outside a closed subgroup by an open
subgroup containing it. Quotienting by the closed subgroup gives a Hausdorff
nonarchimedean abelian group. An open subgroup inside the complement of the
point's nonidentity quotient class pulls back to the required open overgroup.
The published
`WeilReciprocityUniqueness.exists_finiteAbelianExtension_of_isOpen` realizes
that overgroup as the kernel of restriction to an actual finite abelian
extension. Agreement in that restriction then forces membership in the
overgroup, a contradiction. Thus finite restriction images recover the
original closed subgroup. The equality criterion for two closed subgroups
follows.

The construction and proof are derived from the existing topological
abelianization and finite-extension definitions and the cited published
fixed-field bridge. No additional literature theorem is asserted.

## Absolute ramification image reduction

`localAbelianUpperRamificationGroup_isClosed` proves closedness of the
literal abelianization image of the actual absolute upper group, for every
real index. The absolute group is closed in the compact actual absolute
Galois group. Its continuous image is therefore compact, and the
abelianization is Hausdorff. This proof uses no reciprocity assertion.

`localAbelianUpperRamificationGroup_map_restriction` takes
`AbsoluteUpperFiniteImage F` explicitly. For every actual finite abelian
extension, composing its abelian restriction with the abelianization
projection is the actual absolute finite restriction. Thus the assumed
absolute arithmetic theorem computes the finite image of the literal
abelianized upper group, for every index at least `-1`.

`absoluteReciprocityRealUnitImages_of_finite` takes the full-universe
`FiniteReciprocityRealUnitImages` and the universal absolute finite-image
theorem as explicit hypotheses. For every prime, every `PadicField.{u} p`,
every supplied `TopologicalData`, every continuous reciprocity candidate
with the stated geometric relation, and every nonnegative real index, it
proves exactly `AbsoluteReciprocityRealUnitImages`. The image of the
corresponding ceiling-level unit subgroup is compact by
`T.isCompact_unitFiltration` and continuity of the candidate map. It is
closed in the Hausdorff abelianization. The absolute abelian upper group is
closed by the preceding lemma. Their restrictions to every actual finite
abelian extension agree: finite reciprocity computes the first image at
that extension's canonical realization, and the absolute finite-image
theorem computes the second. The closed-subgroup equality criterion then
identifies the two literal subgroups.

`absoluteReciprocityHigherUnitImages_of_real` specializes the real formula
to natural indices, whose natural ceilings equal themselves.
`absoluteReciprocityInertiaImage_of_higher` uses
`T.unitFiltration_zero` and takes the universal `AbsoluteUpperInertia`
comparison explicitly to identify the zero endpoint with actual inertia
for every supplied topological realization.
`absoluteReciprocityImages_of_finite` packages these deductions as the
conjunction of the first three published absolute reciprocity targets.

This module is a conditional reduction. It proves neither finite
reciprocity nor absolute finite-image arithmetic nor the absolute
inertia comparison. It supplies no proof of the full
`AbsoluteUpperReciprocityTheorems` until those inputs are discharged and
the two conductor clauses are proved separately. All equalities use
actual subgroup images; none is replaced by a closure. No injectivity or
surjectivity of the reciprocity candidate is assumed in this reduction.

## Verification

The complete module builds in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with zero errors and warnings.
Inspection of `absoluteReciprocityImages_of_finite` reports the unrestricted
universe parameter `u` and only `propext`, `Classical.choice`, and
`Quot.sound` as axioms. Independent semantic review and publication remain
separate requirements.
