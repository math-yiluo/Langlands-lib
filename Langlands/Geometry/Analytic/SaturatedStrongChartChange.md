# Strong pullback recovery on a saturated source atlas

This internal construction works over a complete ultrametric normed field with
actual indexed affinoid atlas presentations. The source atlas has
`HasAllLocalDomains`: every local full domain is the image of an original source
chart. This property is proved for the constructed saturated atlas in
`SaturatedAtlasDomainClosure`. The target atlas is arbitrary.

For a supplied `StrongHom`, `changeTargetPullback` starts with its bounded
pullback from one admissible target chart and constructs a bounded pullback from
any other admissible target chart. It applies the actual finite-cover chart
change to the unchanged source chart algebra. The image condition follows from
the supplied map's ambient chart equation. The construction uses no supplied
pullback from the new target chart.

`pullback_eq_changeTargetPullback` proves that this construction recovers exactly
the supplied pullback from the new target chart. A finite common-target-chart
cover is pulled back to full domains in the source chart. Source saturation
replaces each such full domain by an original source chart with the same locus
and an actual bounded algebra isomorphism over the containing source algebra.
Transporting the second pullback leg along this isomorphism gives a map from the
common target subchart. The original strong restriction equation and full-domain
factorization uniqueness identify this map with the supplied strong pullback on
that source chart. A second original strong restriction equation, now to the new
target chart, gives exactly the local bounded descent equation. Separation of
algebra elements on the finite original-source-chart cover proves the global
equality of the complete bounded maps.

`pullback_isMapChartChange` consequently proves the full universal chart-change
law for the two supplied pullbacks. This law allows every presented affinoid
test algebra, every bounded coefficient map, and every bounded factorization
through a common original target subchart.

The construction and proof use the imported actual domain pullbacks, original
chart refinements, bounded chart change, and algebra separation. This is internal
provenance; no new external-source attribution is made. There is no inference of
algebra-map equality from equality on spectrum points. No saturation assumption
on the target, directedness, greatest chart, reducedness, or nonempty-spectrum
condition is imposed. Full strong composition and analytic sites remain further
work.
