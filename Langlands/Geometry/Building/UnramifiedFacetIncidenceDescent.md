# Facet incidence descent for a supplied semilinear action

This internal derived construction specializes the geometric comparison in
`ValuationBuildingFacetIncidenceEmbedding` to the actual maximal unramified
extension and an arbitrary supplied `MaximalUnramified.SemilinearApartmentData A`.
It uses this same supplied action throughout; it does not replace it by the
coefficient action obtained from separate Galois-stability data.

`A.fixedLocus` is the subset fixed pointwise by every `A.action σ`.
`A.FixedFacet` retains an original full upstairs facet meeting this subset.
`A.fixedFacetPart` is its intersection with the fixed locus.
`A.IncidentFixedFacets E` consists of those full facets meeting the fixed locus
and incident above `E` for the original upstairs relation `C.FacetPrecedes`.
Meeting the fixed locus is the definition used here; invariance of a full
facet under the action is not asserted.

Let `B` be local-field valuation-building data, `C` the supplied maximal
unramified building, `e` a map of their reduced quotients, and `a` a real affine
apartment map. The hypotheses are:

- `A.action σ (e z) = e z` for every `σ` and `z`;
- every point fixed by all `A.action σ` is in the image of `e`;
- equivariance of `e` under `rationalExtend`;
- compatibility of `e` and `a` on the original apartments;
- exact pullback under `a` of every target affine-root facet;
- source apartment axioms and common source apartments.

All data are at the same arbitrary universe `u`. No injectivity of `e` or `a`
is needed. The first two hypotheses give `range_eq_fixedLocus`.
Replacing `range e` by this fixed locus in the previously constructed
`facetRangeEquiv` gives `fixedFacetOrderIso`. Its forward map retains exactly
`B.facetLift C e`, and its explicit source and target orders are the original
incidence relations. No global order instance is installed.

`image_eq_fixedFacetPart` identifies the image of each source facet with the
fixed part of its full upstairs lift.
`image_closure_eq_inter_fixedLocus` gives the analogous identity for the original
combinatorial closure. Both follow from the previously proved image identities
and the equality of `range e` with the supplied fixed locus.

`incidentFixedFacetOrderIso` restricts the same equivalence to all facets
incident above any chosen source facet `Fc`. The exact incidence comparison
`facetPrecedes_facetLift_iff` proves that the defining subtype predicates
correspond and proves preservation and reflection of incidence on this
restriction. Its forward map remains the full lift of the underlying source
facet, as recorded by `incidentFixedFacetOrderIso_val`.

The provenance is entirely internal: this is restriction and relabeling of
the published facet comparison using the two supplied fixed-point hypotheses.
For `UnramifiedFacetParabolicOrderStatement`, take
`B = P.toValuationBuildingData`; the target supplies these comparisons and
fixed-point hypotheses explicitly. Its building axiom supplies common
apartments through `SatisfiesBuildingAxiom.hasCommonApartments`.
The other building and descent premises remain available to the further
special-fibre argument. This construction establishes the geometric
correspondence of incident facets. Identifying their actual special-fibre
model images with parabolic subgroup functors, and proving the resulting
parabolic bijection, are separate obligations.
