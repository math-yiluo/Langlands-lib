# Incidence under exact building facet restriction

This is internal derived content combining exact affine closed-facet pullback,
the existing full-facet restriction embedding, and the published chart formulas
for combinatorial building closures. It introduces no literature translation.

The supplied data and hypotheses are those of `facetRestrictionEmbedding`: a
valuation building `B` over a local field, integer-valued building data `C`,
a rational-point homomorphism `ρ`, quotient point map `e`, affine apartment map
`a`, downstairs apartment axioms and common point apartments, equivariance,
apartment compatibility, and exact pullback of affine facets through points of
the apartment image. The conclusions use the original full facets and
combinatorial closures, at arbitrary universe `u`. No injectivity or
surjectivity of `e` is required.

`map_mem_buildingFacetClosure_at_iff` puts two arbitrary downstairs quotient
points in a common translated apartment. The chart formulas express both
containing closed facets as images of the affine closed facets. Exact affine
facet pullback implies exact closed-facet pullback by
`preimage_facetClosure_eq_of_preimage_facet_eq`. Upstairs chart injection
identifies a coordinate witness, proving both membership directions.

`preimage_buildingFacetClosure_facetRestrictionEmbedding` then identifies the
complete inverse image of each assigned upstairs closed facet with the entire
downstairs closed facet. As with the open-facet embedding, this includes points
outside the chosen presentation.

`facetRestrictionEmbedding_facetPrecedes_iff` preserves and reflects incidence
of full building facets. Choose a point in the lower facet. In either building,
its membership in the upper closed facet is equivalent to the face incidence,
by the existing partition and closure lemmas. The image point belongs to the
assigned upstairs lower facet, and the complete closed-facet pullback proves
the required equivalence.

Finally, `facetRestrictionOrderEmbedding` equips this same function embedding
with exactly the two existing explicit incidence orders. This last construction
also takes injectivity of the downstairs apartment map, as required to form
its existing partial order. The application formula agrees definitionally
with `facetRestrictionEmbedding`. These geometric conclusions do not assert
the host model-image parabolic correspondence.
