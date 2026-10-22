# Identification with the ordinary product of skyscrapers

Author: Worker 61. Reuses the published equivariant sheaf interfaces of
Worker 13 and the companion stalk-family construction.

This module proves that, after forgetting equivariance, `zeroSheaf F` is
the categorical product of Mathlib's actual skyscraper sheaves
`skyscraperSheaf x (F.stalk x)` over all points `x` of the space.
`skyscraperRead` identifies a skyscraper section with its coefficient when
the open contains its point, and `skyscraper_map_read` proves that this
identification commutes with restriction. `familyEvaluation` evaluates a
stalk family, and `familyEvaluation_restrict` proves its compatibility with
restriction. `skyscraperProjectionApp` combines evaluation with the unique map
to the terminal object on opens not containing the point;
`skyscraperProjectionApp_read` records its value on opens containing the
point. `skyscraperProjection` is the resulting morphism of ordinary sheaves.

`skyscraperFan` is the resulting product cone.
`skyscraperFanLift` constructs its universal map by assembling the
pointwise components of an arbitrary cone. `skyscraperFanIsLimit` proves
the projection equations and uniqueness, using evaluation on each point.
`skyscraperProductIso` is the resulting canonical categorical isomorphism.
Thus the product description is a proved construction rather than a supplied
identification or a descriptive name.

Universes, coefficients and continuity hypotheses are those of `Zero.md`.
This identifies an ordinary-topological product after forgetting equivariance.
It does not identify the object with Berkovich's product on an equivariant
analytic étale topos, nor assert exactness or acyclicity.

Source provenance and the exact retained original reading extents are in
`Stalks.md`: Berkovich's unfinished 1995–1996 manuscript sections 1.4–1.5
and Harris 1999 section 2. The product universal-property proof is internal
categorical infrastructure. Mathlib dependencies are ordinary skyscrapers,
sheaf limits and module linear maps at
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.
