# Hyperbolic projection and quadratic decomposition

This internal derived module takes a hyperbolic pair for the published
quotient-valued quadratic form. It defines the two-coordinate projection
`z ↦ h(z,y)x + h(z,x)y` and its complementary remainder as linear maps over `D`.
The hyperbolic projection fixes both members of the pair and is idempotent.
The remainder pairs to zero with both of them, so its range is polar orthogonal
to the hyperbolic plane.

Polarization and singularity of the two lines give
`q(ax + by) = [a σ(b)]` in `D / Alt(σ)`. Applying this formula to the plane
projection gives the implemented decomposition of `q(z)` as the sum of its
plane and remainder values. All results follow from the preceding hyperbolic
pair and quadratic-form identities; they use no characteristic restriction.
