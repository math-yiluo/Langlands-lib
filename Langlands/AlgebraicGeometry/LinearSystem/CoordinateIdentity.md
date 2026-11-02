# The linear system of projective coordinates

This derived construction packages the actual degree-one twist on
projective space over an arbitrary commutative ring as a line bundle. Its
coordinate sections have no common zero, as follows from their published
generation opens and the coordinate open cover.

For a scheme morphism whose image lies in a coordinate chart, the ratio of two
pulled-back coordinate sections is the pullback of the projective coordinate
ratio. The proof uses the coefficient identity for the actual coordinate sections
and uniqueness of a coefficient relative to a frame.

The affine chart calculation identifies the composite of the localization
section map with pullback along the actual affine Proj chart inclusion. The
proof factors the inclusion through the actual affine-chart isomorphism and
cancels that isomorphism.

The chart algebra is generated over the base ring by the degree-zero coordinate
ratios, using the published `ProjSpace.adjoin_range_ratio`. On these generators,
the localization map associated to the coordinate linear system agrees with the
canonical affine section isomorphism. The ratio calculation proves equality on
the ratio generators. Naturality of the affine section isomorphism proves
equality on base constants. Algebra-adjoin induction then proves equality on
the whole chart algebra.

The associated point map on each affine chart is consequently the original
chart inclusion. The affine cover detects equality of scheme morphisms, proving
`linearSystemMap_projectiveCoordinates`: the linear system of the actual
coordinate sections is the identity morphism.

The relative coordinate sections are the pullbacks of the integral coordinate
sections. Their generation follows by pullback. Naturality of the integral
linear-system map and the integral coordinate identity identify their integral
map with the projection to the integral model. The base and integral projections
jointly detect equality in relative projective space; hence
`relativeLinearSystemMap_relativeProjectiveCoordinates` is its identity morphism.

All results are derived from the imported polynomial-Proj, section-ratio and
linear-system constructions; no new external source assertion is used. The
proof of chart generation remains in the imported FLT port with its original
attribution. This unit supplies coordinate recovery, with arbitrary base ring
and arbitrary base scheme in universe `u`. It does not construct a tautological
sheaf on a glued projective bundle, prove a cubic embedding or a quotient
theorem, or prove the ordinary moduli representability assertion.
