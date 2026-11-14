# First-projection descent for local-isogeny graphs

This is a derived support for split-isogeny realization, using the actual
graph base-change construction, actual root-datum transport, the
algebraically closed first-projection isomorphism, maximal-torus base change,
geometric reductivity and fpqc reflection already available in the Library.
There is no additional literature assertion.

Work over an arbitrary field `k` in an arbitrary universe `u`. The source
and target are smooth affine group schemes, with connected source. A
`SimpleIsogenyGraph D` supplies an actual graph, the two projections, a
split source torus and local isogenies. Assume that the source is connected
reductive, its supplied torus is maximal, and the graph itself is connected
reductive. The target torus is split. Supply finite reduced root data on
both actual pairs of torus lattices, the required lattice
finite-generation instances, proofs that these are the actual ambient
root data, an isogeny between the root data and equality of its weight map
with the pullback of the actual torus map. No restriction to factor-one
isogenies is imposed.

`SimpleIsogenyGraph.first_isIsoOfReductive` proves that the first actual
projection is an isomorphism over `k`. It passes to `AlgebraicClosure k`
and uses the actual pulled-back graph. Geometric reductivity supplies
reductivity of the extended source and graph. The maximal source torus
remains maximal. Actual lattice pullback supplies both finite-generation
instances, transports the root data and their reducedness, and conjugates
the isogeny maps while retaining every root factor. Compatibility of
character pullback with the actual torus map supplies the extended weight
identity.

These inputs apply `firstProjectionIsoOfReductive` over the algebraic
closure. The identity for the first projection of the actual pulled-back
graph identifies its invertible map with the pullback of the original
projection. The published fpqc isomorphism reflection for field
extensions then proves the claim over `k`.

`firstProjectionIsoOfReductiveField` packages this result as an
isomorphism from the supplied graph group to the source. Its `_hom`
theorem identifies its map with the original first projection
definitionally. Neither the graph nor its local maps are replaced in this
descent.

The result still takes graph reductivity as an explicit hypothesis; it
does not provide target coverage, the second projection's isogeny
property, or the final realization theorem.
