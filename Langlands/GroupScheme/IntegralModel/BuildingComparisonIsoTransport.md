# Building comparisons through actual integral isomorphisms

For actual affine group schemes `G` and `H` over the same nonarchimedean local
field `F : Type u`, this internal construction transports a supplied
`BuildingComparison M` through a compatible integral-model isomorphism
`e : M.Iso N f`, where `f : G ≅ H`. All universes, original integral models,
generic identifications and rational-point actions are retained.

`toMetricRealization` copies the five metric fields of the given comparison on
its existing quotient. `mapIso` uses the actual full valuation-building datum
`D.building.mapIso f` and its quotient equivalence `Q`. The metric is the inverse
equivalence induced metric supplied by `MetricRealization.mapIso`, including
completeness, the full NPC midpoint inequality, isometry of the existing target
action and continuous orbits for exactly `rationalPointTopology F H.X`.
Its distinguished point is `Q D.point`. The full affine-root comparison proves
that this point is both a vertex and special.

For the integral subgroup identity, the compatible integral-model isomorphism
maps the original `M.integralPoints` onto the original `N.integralPoints`.
The supplied comparison identifies the first subgroup with its norm-one point
stabilizer, and the actual quotient transport maps that stabilizer onto the
norm-one stabilizer of `Q D.point`. Thus the result identifies exactly the
original target model image, including its common rational-character kernel.

If a target point `y` is fixed by the original target model image, equivariance
and the same integral-subgroup map show that `Q.symm y` is fixed by the original
source model image. The given comparison's uniqueness implies
`Q.symm y = D.point`; applying `Q` gives `y = Q D.point`.

`ofGroupIso` accepts an abstract integral isomorphism and uses
`Iso.ofGroupIso`, whose actual generic map is computed from its coefficient
pullback and both supplied generic identifications. No prescribed generic map
is assumed to extend integrally. The building and point equations identify
exactly the data used in these constructions.

The provenance is internal composition of the integral-image transport,
the full quotient and affine-root transport, and the metric realization
transport. This unit assumes a comparison and an integral isomorphism. It
asserts neither their existence nor the unconditional
`BuildingComparisonStatement`, and introduces no new literature assertion.
