# Localization of affine-open coordinate rings

This internal compatibility construction supports the affine-open clauses of
`AnalytificationCenterStatement`. It is derived from the published coordinate-ring
and restriction definitions and Mathlib's affine-scheme localization theorem;
no additional result is attributed to the original literature.

For a scheme `X` over a commutative ring `K`, an affine open `U`, and a section
`g` in `Γ(X, U)`, `CenterRange.basicOpenGenerator f U g` is the corresponding
element of the actual coordinate algebra `CoordinateRing (structureMap f U)`.
It is obtained from the inverse of the canonical global-section isomorphism
`U.topIso`.

`CenterRange.isLocalization_restriction_basicOpen` proves that the actual
coordinate ring of `X.affineBasicOpen g`, with the algebra structure induced by
`restriction f (X.affineBasicOpen_le g)`, is a localization away from that element.
The proof transports Mathlib's `IsAffineOpen.isLocalization_basicOpen` through
`U.topIso` on the source and the basic open's `topIso` on the target. Compatibility
of the algebra structures follows from `Scheme.homOfLE_appTop` and functoriality
of the structure presheaf. No finite-type or norm hypotheses are needed.
