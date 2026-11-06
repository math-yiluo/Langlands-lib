# Vertex permutations for a supplied realization

This internal construction starts with actual `ValuationBuildingData G`
and a supplied `B.PolysimplicialRealization R`, at arbitrary universe `u`
over a nonarchimedean local field. Its sole additional premise is
`hR : R.IsFaceCompatible`. It requires neither apartment axioms nor a
Tits-system witness.

`RealizationApartmentTransport.facetTranslateOrderIso` already transports
the original rational-point action on facets of the existing quotient
through the realization bijection. `facetTranslateOrderIso_one` and
`facetTranslateOrderIso_mul` prove its action laws by applying `R.realize`
and using the corresponding laws of `BuildingFacetAction`.

`vertexTranslateEquiv` uses `FacetOrderVertexEquiv` to recover the unique
vertex permutation from this facet order isomorphism. The generic helper
identifies vertices with minimal facets, which are their singleton sets.
`vertexTranslateEquiv_image` gives the exact image of every facet.
`vertexTranslateEquiv_image_iff` compares an equality of vertex images
with the image under the original rational-point action on the quotient.
The latter is exactly the facet-image equivalence required in the
existing `IsPolysimplicialAction` definition. Injectivity of `R.realize`
proves the reverse implication.

`vertexTranslateEquiv_unique` shows that any vertex permutation
satisfying that original-action comparison equals the recovered one:
apply the comparison to the prescribed translated facet, and then use
the generic uniqueness theorem on singleton facets.

Uniqueness also gives the identity and multiplication laws for
`vertexTranslateEquiv`. In the multiplication case, the image under the
composite is the iterated facet image, and the original facet action
law identifies it with the image for the product. `vertexActionHom`
packages the laws as a homomorphism to the permutation group of
vertices. `vertexTranslateEquiv_inv` is its inverse law. No global
action instance is installed.

`isPolysimplicialAction_iff_vertexTranslateEquiv` isolates the remaining
obligation: the supplied realization has a polysimplicial action if and
only if these recovered vertex permutations satisfy the existing
`IsPolysimplicialAutomorphism` predicate. Forward implication uses
uniqueness; reverse implication supplies the already proved exact
facet-image comparison.

In particular, this file does not prove that the recovered vertex
permutation acts through one permutation of the simplicial factors
and simplicial isomorphisms on those factors. That condition in
`IsPolysimplicialAutomorphism` remains open. Existence of the actual
data and realization, the building axioms and the unconditional
root-valuation construction also remain separate obligations.
All results here are derived from the imported Library definitions
and the two internal facet-action constructions; no new external
assertion is used.
