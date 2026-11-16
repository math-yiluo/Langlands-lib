# Actual global-chart normalization through order-linear transitions

This internal module proves an actual rational coherence equation
for a globally coordinated formal module with a full-order action,
restricted to a specified principal-open cover.

The scalar ring is a commutative domain with its specified fraction
field, the coefficient ring is any commutative scalar algebra, the
acting order is any algebra ring, and the coordinate type is finite.
The principal cover may be infinite. Test algebras use the
coefficient-ring universe.

`globalOrderChartQuasi_transition` starts at the tested global
module, passes into its first chart through the inverse of the
actual global-chart isomorphism, and then applies the actual
full-order transition to the second chart. The resulting entire
quasi-isogeny equals the inverse global-chart isomorphism into
that second chart.

The proof uses full-order quasi-isogeny extensionality, then the
actual tensor inclusion's composition equation. The remaining
integral formal maps have compositions of identity coordinate
series, so they agree by formal-map extensionality. It does not
infer formal-map equality from equality on evaluated points.

The provenance is internal from the constructed global-cover
atlas, global-chart identifications and full-order transition
isomorphisms. No framing, height or representability assertion is
made here.
