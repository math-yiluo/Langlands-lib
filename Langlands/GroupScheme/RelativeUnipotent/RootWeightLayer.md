# Exact-weight additive coordinates at positive cutoffs

This internal derived construction extends `RootWeightFiltration` using the
positive-cutoff group equivalence of `HeightPositiveLayer` and the original
root-coordinate equivalences of `RootHeightLayer`. It uses a supplied
`RootHeightChart C` and `RootWeightData C`; it does not construct those data for
a parabolic.

Term `d` has cutoff `d + 1`. The exact support consists of indices of weight
`d + 1`, and its finite enumeration labels the additive coordinates, including
an empty support. No root products are reordered. Each root parameter is read
using the original chart's isomorphism onto its actual point subgroup.

On every scheme test, the exact-factor product is isomorphic to the actual
successive subgroup quotient by `HeightLayer.layerEquivOfPos`. Composing its
inverse with the quotient projection and the exact parameters defines the
homomorphism `layerCoordinates` to the multiplicative form of the additive
section-coordinate group. The cutoff is always positive, so no positivity
assumption on all ambient weights is needed.

The proof `layerMap_coordinateFactors` collects the original chart coordinates
of a point in term `d`. Coordinates below `d + 1` vanish; coordinates above
`d + 1` lie in the next subgroup and disappear in the quotient. Applying the
inverse factor-product equivalence therefore reads precisely the original
coordinates of weight `d + 1`, as `layerCoordinates_apply` proves.

This module supplies pointwise additive quotient coordinates. Representation of
the quotient map, its fppf properties and exact kernel, a finite series, and the
construction and descent for a supplied relative radical remain separate
obligations. No external source translation is claimed.
