# Combinatorial closed facets of the actual valuation quotient

This internal construction concerns supplied actual `ValuationBuildingData G`
over a nonarchimedean local field, at arbitrary universe `u`. The definition
`buildingFacetClosure Fc` is the union of the original building facets `Fd`
with `FacetPrecedes B Fd Fc`. These are subsets of the original
`B.ReducedBuilding`, with its original rational-point action. The definition
uses no new point carrier and requires no structural hypotheses.

Under the full `B.SatisfiesApartmentAxioms`, the module proves the exact
coordinate formula: if `Fc` is the image under a translated apartment map of
the affine facet through `a`, then `buildingFacetClosure Fc` is the image
under that same map of `AffineRootSystem.facetClosure B.affineRoots a`.
This formula needs neither chart injectivity nor opposite-factor pairs. The
word closure here refers to the combinatorial union of faces and the existing
affine-root closed-side formula; no assertion about the topological closure
in a topology on the quotient is made.

The entry `buildingFacetClosureEmbedding` is an injective map from the
existing `BuildingFacet B` to subsets of the same reduced quotient, sending
each facet to that union. This embedding retains the full apartment axioms
and injectivity of the original apartment map. The theorem
`facetPrecedes_iff_buildingFacetClosure_subset` identifies the existing
incidence relation with inclusion of those closed subsets under these same
premises.

## Implemented proof

Every facet lies in its own closed facet by the existing reflexivity of
`FacetPrecedes`. Every apartment containing the upper facet contains all its
lower incident facets, using
`BuildingFacetIncidence.subset_apartment_of_facetPrecedes`; it therefore
contains their union. The facet partition from `BuildingFacetPartition`
shows that a point is in the union exactly when its unique containing facet
precedes the upper facet. It also shows that one point of an original facet
in the union forces the whole facet to precede the upper facet. Consequently,
`FacetPrecedes B Fc Cc` is equivalent to `Fc.val` being contained in
`buildingFacetClosure Cc`. These deductions use the apartment axioms alone.

For the coordinate formula, start with a lower incident facet and a chart
witnessing that incidence. The prescribed upper representative `a` has an
image in the upper facet, hence has coordinates `c` in the witnessing chart.
The quotient relation and the AS4 singleton sharp-fixer comparison, packaged
in `exists_normalizer_eq_on_translated_facetClosure`, give a normalizer
element taking `c` to `a` and agreeing on the whole closed facet of `c`.
Every lower point lies in that closed facet by the existing affine face
relation. AS5 preserves the affine roots, so the changed coordinates lie in
the closed facet of `a`. This proves containment in the stated image. For
the reverse containment, the affine facet through any point in the closed
facet of `a` is a face of the facet through `a`; its translated image is one
of the lower incident facets in the defining union.

Finally, transitivity from `BuildingFacetIncidence` makes taking closed
facets monotone under incidence. The preceding containment characterization
provides the converse. Equality of closed facets thus gives incidence in
both directions, and antisymmetry gives equality of the original facets.
This proves the injection used by `buildingFacetClosureEmbedding`.

## Provenance and scope

This is an internal deduction from the original `AffineRootSystem` closure
formula, `ChamberFiltration.mem_facetClosure_of_isFaceOf`, the original
quotient relation and normalizer action, and the separately submitted
`BuildingFacetPartition` and `BuildingFacetIncidence` constructions. Their
unchanged helper `ApartmentFacetConstruction` is also included when needed
for integration. No independent external mathematical assertion is added.

AS5 and the other full apartment axioms remain premises. Chart injectivity
remains a premise of the embedding and inclusion-of-closed-facets
characterization; it is not used in the coordinate formula. This module
does not construct general valuation data, a polysimplicial realization, or
the five witnesses of `RootValuationBuildingConstructionStatement`.
