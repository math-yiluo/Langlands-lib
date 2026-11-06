# Recovering a vertex bijection from the facet order

This internal construction concerns the existing finite-product
`AbstractBuilding.PolysimplicialComplex` definition. Let `K` and `L` be two
such complexes, with independent index and vertex universes, and let
`e : K.facets ≃o L.facets` be an order isomorphism of their actual facet
sets. No field, group or geometric realization is involved.

`minimal_facets_iff` identifies minimal facets with singleton vertex sets.
A facet is nonempty; any vertex it contains supplies a singleton facet
below it. Minimality then forces equality with that singleton. Conversely,
any nonempty facet below a singleton equals that singleton.

`vertexMinimalFacetEquiv` is the equivalence sending a vertex to its
singleton minimal facet. The equivalence is constructed from the bijectivity of the singleton
map; minimality proves its surjectivity, and its inverse recovers the
unique vertex of a minimal facet.
`facetOrderVertexEquiv` composes this equivalence with the induced order
isomorphism of minimal facets and the inverse equivalence for `L`.

`facetOrderVertexEquiv_singleton` gives the image of each singleton under
`e`. A vertex belongs to a facet exactly when its singleton lies below
that facet. Order preservation therefore proves
`facetOrderVertexEquiv_mem_iff`. Surjectivity of the vertex equivalence
then gives `facetOrderVertexEquiv_image`: its set image of each facet is
exactly the facet prescribed by `e`.

`facetOrderVertexEquiv_unique` proves that this is the only vertex
bijection inducing `e`: compare the images of each singleton facet.
The proofs use only the imported definitions, facet nonemptiness and
singleton membership, and Mathlib's transport of minimal elements along
an order isomorphism.

`facetOrderVertexEquiv_refl`, `facetOrderVertexEquiv_trans` and
`facetOrderVertexEquiv_symm` show that this reconstruction preserves the
identity, composition and inverse. Uniqueness proves the first two by
comparing the images of facets. The inverse case applies the inverse
vertex equivalence to the known image equality.

This constructs a vertex bijection preserving the specified facets. It
does not construct a permutation of the simplicial factors or the factor
isomorphisms required by `IsPolysimplicialAutomorphism`. That additional
condition is retained when using this construction for building actions.
