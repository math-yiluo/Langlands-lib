# Incident root images for actual neutral components of full fixer models

This internal adapter works at arbitrary universe `u` over the integers of
the actual inertia fixed field of a nonarchimedean local field. It takes
integer-valued building data `C` and two supplied relative-component models
`M`, `M'`. The full models' integral points are the character-valuation
kernel intersected with the pointwise fixers of the apartment images of
`Ω`, `Ω'`. The supplied comparison `ψ` is a map from the source neutral model
to the target neutral model over the generic identity. Smoothness of both
neutral models is part of the supplied relative-component data.

The actual integral torus is `unramifiedNeutralSplitTorusData C M Ω hM`.
Its root models, generic root inclusions, and integral root-model maps are
the existing constructions inside the target neutral component.
`unramifiedNeutralRootModel_integralPoints_eq` identifies the generic image
of each such root model's integral points with the target apartment root
fixer. It combines the general integral-root image formula with
`rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer`.

Assume the root fixer on `Ω` is contained in the root fixer on `Ω'`.
The latter root fixer lies in the source neutral integral subgroup by its
own exact root-intersection formula. Smooth homomorphism extension over the
inertia-fixed integers therefore extends the target root model's prescribed
generic inclusion to the source neutral model. This is
`unramifiedNeutralRootModelLift`. Generic rigidity identifies its composite
with `ψ` with the original target root-model map.

`unramifiedNeutralRootImageFactor` takes the special fibre of the lift and
composes with the canonical schematic-image projection for `ψ`.
Its compatibility theorem recovers the target root-model map after the
image inclusion. Thus `unramifiedNeutralRoot_range_le_image` contains the
entire root-model residue image in the actual comparison image on every
test scheme over the residue field.

For nonempty subsets `Ω`, `Ω'` of incident facets `Fa`, `Ca`, with `Fa` a face
of `Ca`, the existing adapted cocharacter gives equality of their root
fixers for every root positive on that cocharacter. The construction
`unramifiedNeutralIncidentPositiveRootImageFactor` and its specifications
apply the general lift and image factor to those positive roots. These
claims do not require boundedness or a separately supplied root-fixer
comparison.

The derivation adapts the zero-fixer incident-root construction to the
actual neutral components of supplied full one-fixer models, using their
published integral torus and root-intersection formulas. It assumes no
identification of a neutral subgroup with a globally specified zero-point
subgroup. It does not construct the supplied models, prove containment
of the entire special-fibre unipotent radical, establish parabolicity, or
prove an exact reduction-preimage formula.
