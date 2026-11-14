# Positive root-model images for incident unramified facets

This derived construction works at arbitrary universe `u` over the actual
integers of the inertia fixed field of a nonarchimedean local field `F`.
Let `C` be integer-valued building data for an affine group `G` over that
field, and let `E` be any unramified zero datum. Let `N`, `N'` be actual
integral models characterized by the zero fixers of apartment subsets
`Ω`, `Ω'`, respectively. Assume `N` is smooth and let `ψ : N' → N`
extend the identity of the generic group.

The target's integral torus and integral root models are the actual
constructions from `UnramifiedZeroFixerRoots`. No integral-torus,
root-model, or root-image premise is supplied here.

`unramifiedZeroFixerRootModelLift` assumes that the root fixer on `Ω`
is contained in the root fixer on `Ω'`. The target root model's exact
integral-point image is its root fixer on `Ω`. The inclusion hypothesis
therefore places that image in `N'.integralPoints`. The published smooth
homomorphism extension theorem over the inertia-fixed integers extends
the generic root inclusion to a map from this actual root model into `N'`.
Generic rigidity proves that its composite with `ψ` is the original
target root-model map. Smoothness of `N'`, boundedness, and nonemptiness
of the subsets are not hypotheses of this general construction.

`unramifiedZeroFixerRootImageFactor` takes the special fibre of this
lift and composes it with the canonical projection onto the schematic
image of `ψ` on special fibres. Its compatibility theorem recovers the
original target root-model map after the closed image inclusion.
`unramifiedZeroFixerRoot_range_le_image` consequently places the
whole image of this root-model special fibre in the actual schematic
image on every test scheme over the residue field. This is stronger
than containment only on residue-field points.

The incident-facet specialization allows `Ω`, `Ω'` to be any nonempty
subsets of facets `Fa`, `Ca`, with `Fa` a face of `Ca`. Neither subset
has to be a whole facet. The helper
`KPApartmentData.rootFixer_eq_of_nonempty_subset_facet` identifies
the root fixer of a nonempty subset of a facet with that of the whole
facet: antitonicity gives one inclusion, and evaluating at one point
of the subset with facet constancy gives the other. This helper
retains AS4 explicitly for general apartment data.

For the actual integer-valued building data, the existing AS4 theorem
discharges that premise. The single adapted generic cocharacter
`C.incidentFacetCocharacter hCa hFaCa` then gives equality of root
fixers on `Ω` and `Ω'` for every root positive on it.
`unramifiedIncidentPositiveRootImageFactor` and its two specification
theorems apply the preceding lift and image construction to each such
root. They retain no boundedness or independently supplied filtration
equality premise.

The provenance is internal: actual zero-fixer root models, smooth
homomorphism extension, generic rigidity, the schematic-image
factorization, facet constancy, and the proved adapted-cocharacter
comparison supply all steps. The unit does not identify root-model
residue images with residue-root subgroups, prove that the actual
descent map sends the two downstairs facets into incident upstairs
facets, establish parabolicity, or prove the exact reduction-preimage
assertion. These remain obligations in the host task.
