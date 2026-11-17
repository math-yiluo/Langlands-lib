# Affine neighborhoods and gluing for structurally etale atlases

This internal extension of `AffineAtlasNeighborhoods` and
`AffineAtlasChartReduction` removes their structural monomorphism premise.
The sheaf has closed diagonal, and its etale scheme atlas has an etale
composite to a scheme. No affineness or finiteness condition is placed on that
scheme or the original atlas.

At each atlas point, choose an affine open neighborhood in the target scheme,
form the scheme and sheaf pullbacks, and choose an affine open neighborhood
around a lifted point in the scheme pullback. The resulting chart is etale,
its structural composite is etale by base change, and the pullback sheaf is
open in the original sheaf. This constructs `AffineAtlasNeighborhood`.

Its sheaf has closed diagonal by the affine pullback lemma. The compact affine
chart-image theorem supplies a scheme representing the local image of this
chart. The open image inclusion, followed by the original open restriction,
is an open scheme chart of the original sheaf. Yoneda gives the chart source
map into that representative and its compatibility with the original atlas.
The chosen source point lies over the original atlas point.

The published point-lifted open-chart gluing theorem now represents the entire
fppf sheaf, provided the original etale chart is surjective. The proof combines
published affine-cover and gluing APIs with the separately submitted separated
etale image descent; it does not assume the generic schemehood criterion.
