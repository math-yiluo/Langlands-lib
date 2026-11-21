# Compact open groups of units from ultrametric coordinates

Equip a normed algebra with continuous linear coordinates `e` in a
proper ultrametric normed space. The algebra has summable geometric
series. `UnitsCoordinateBallStatement` says that for every sufficiently
small positive radius, the inverse image of the coordinate ball under
`g ↦ e(g − 1)` is a compact open subgroup of the units, and the same map
sends it onto the ball.

The algebra norm and the operator norms of `e` and `e⁻¹` give a single
quadratic product bound in the coordinate norm. Choose the radius so
that one plus every ball element is a unit and the product bound
contracts at that radius. The formulas for multiplying `1 + x` and
`1 + y` and the ultrametric triangle inequality give multiplication
closure. For the inverse write `(1 + x)⁻¹ = 1 + y`. The identity
`y = −(x + xy)` implies that the coordinate norm of `y` is at most the
radius. If it were larger, the product bound would make both terms on
the right strictly smaller than `y`. The affine map is an open
embedding and maps the subgroup onto the compact closed ball.

This internal lemma allows the torus and transverse spaces in a Weyl
chart to use a split coordinate ball.
