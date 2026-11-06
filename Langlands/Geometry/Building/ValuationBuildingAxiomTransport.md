# Transport of axioms on actual valuation-building quotients

This internal derived unit concerns two supplied `ValuationBuildingData`
for the same actual group over the same nonarchimedean local field. It
does not construct either datum or a source axiom witness. The carriers
and actions are the existing valuation quotients and rational-points
actions.

The entry construction `IsBuildingIso.facetEquiv` restricts the image
operation of a supplied building isomorphism to an equivalence of the
existing `BuildingFacet` types. Its forward operation takes the image by
the quotient equivalence, and its inverse takes the image by the inverse
equivalence. The proof uses the isomorphism's preservation and reflection
of facets and the existing equivalence on sets. Neither a new facet
predicate nor a new building carrier is introduced.

An equivalence equivariant for the identity on actual rational points
identifies the two point-fixer subgroups. Intersecting with the unchanged
actual rational norm kernel identifies the compact stabilizers. The
bounded-open-stabilizer predicates therefore agree: both openness
conditions use exactly `rationalPointTopology F G.X`, and both boundedness
conditions use the same algebraic boundedness predicate on the same
rational points. No topology is transported or chosen on the quotient.

For AS 6, assume a building isomorphism, an affine equivalence of the
actual apartments commuting with their quotient maps, and equality of the
entire transported affine-root sets. Source AS 6 proves target apartment
injectivity by cancelling the quotient equivalence and the apartment
equivalence. A target facet meeting its canonical apartment pulls back to
a source facet meeting the source canonical apartment. Source AS 6
presents it as the image of a full apartment facet. Full root transport
then presents the original target facet as the image of the corresponding
full target apartment facet.

These are internal consequences of the existing `mem_fixer`,
`compactStabilizer`, `HasBoundedOpenStabilizers`,
`HasCompatibleApartmentFacets`, `IsBuildingIso` and
`AffineFacetTransport` definitions and results. The source predicates
encode KP Axiom 4.1.2 and AS 6 of Axiom 4.1.6. The geometric comparison
is the kind required in the intended KP 9.6.6 application; its actual
existence, every-point fixer comparisons, filtration identities and source
witnesses remain separate construction obligations. This unit does not
prove the unconditional `RootValuationBuildingConstructionStatement`.

The provenance is internal and derived. The proofs use subgroup
extensionality, cancellation by equivalences, images and preimages of
sets, and the existing full-root facet-transport theorem. The source
axiom labels identify the imported Library predicates; no new
translation or existence result from the literature is asserted here.
