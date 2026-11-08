# Original simplicial faces on affine torsors

This derived development transports the actual simplex criterion to the
original affine torsor, with independent universes for its vector and point
types. The supplied corrected affine root system and independence of its
entire original facet vertex families remain explicit assumptions.

Full affine root transport identifies the original vertex types through
`transportedVertexEquiv`. The existing exact transport formula for all actual
facet vertices, together with affine invariance of affine independence, proves
`affineIndependent_torsorVertexFinset_transportedRoots_iff`. On a vector space,
the torsor and vector vertex finsets agree by their common exact membership
criterion.

The centroid subset theorem holds on the original torsor. Choose affine
coordinates, transport the entire root system and all actual vertices, and
apply the existing vector-space theorem. Exact vertex transport and
naturality of nonempty centroids return the literal original vertex-finset
equality.

`torsorFacetVertexSimplicialComplex` transports the constructed vector-space
simplicial complex to the original vertex type. Its faces are exactly the
entire original vertex sets `torsorFacetVertexSet Ψ p`; the face
characterization removes the construction's dependence on the supplied
coordinate equivalence. No additional faces or subdivision are introduced.

The entire original vertex sets are finite and nonempty. Their inclusion and
equality are equivalent to inclusion and equality of the original closed
facets, using the torsor vertex-finset incidence theorem. This gives
`torsorClosedFacetSimplicialOrderIso`: the forward map takes a closed facet
to its entire vertex set, order reflection follows from the exact incidence
criterion, and the intrinsic description of all faces gives surjectivity.
The constant one-factor complex then gives
`torsorClosedFacetPolysimplicialOrderIso` and
`isPolysimplicial_torsorClosedFacets_of_affineIndependent`.

These results are internal consequences of the existing full root, vertex and
centroid transport, the exact simplex criterion and Mathlib's affine
independence invariance. They assert no new literature result. They preserve
rank zero but do not prove the independence premise for arbitrary root
systems or construct irreducible factors, the quotient building data or the
host's unconditional axiom witnesses.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
