# Comparison of existing valuation-building quotients

This internal derived construction specializes `ApartmentQuotientComparison`
to two supplied `ValuationBuildingData` for the same actual group over the same
nonarchimedean local field. Both carriers are the existing `ReducedBuilding`;
both actions are their existing rational-points actions. No existence of
valuation-building data or any KP axiom witness is asserted.

Every quotient point belongs to an affine-root facet. Given a supplied
`SatisfiesBuildingAxiom` witness, the realization identifies each such facet
with a combinatorial facet. The chamber-complex property extends those facets
to chambers. BL 3 places the two chambers in one apartment, and the subcomplex
property places their original faces there as well. The definition of the
realized apartment then puts both original points in one translate of the
canonical apartment. This argument uses the supplied building witness; it
does not assume a metric or an additional face-compatibility hypothesis.

The comparison takes an affine equivalence of the actual apartment spaces,
normalizer equivariance of its composition with the target apartment map,
and inclusion of each source sharp point fixer in the fixer of the
corresponding target point. The last inclusion quantifies over every apartment
point, as required by corrected KP Corollary 4.4.5. The universal equivariant
lift gives a map of the existing quotients. Target orbit coverage and
surjectivity of the affine equivalence prove surjectivity. Common source
apartments and injectivity of the target apartment map prove injectivity.

The equivalence preserves the rational-points action in both directions.
In translated apartment charts it uses the same group element and the
supplied affine equivalence. It therefore preserves and reflects apartments.
If inverse precomposition transports the entire source affine-root set
onto the target affine-root set, `AffineFacetTransport` transports exactly
the full apartment facets. Their group translates give preservation and
reflection of all building facets. The resulting equivalence satisfies the
existing `IsBuildingIso` and `IsEquivariantBuildingIso` predicates, with the
identity homomorphism on actual rational points. No root-group filtration
identification is deduced: establishing the root-set equality and the
every-point fixer inclusion in an actual construction remains necessary.

The provenance is the internal quotient universal property derived from
KP Proposition 4.4.4 and corrected Corollary 4.4.5 (book printed pp. 183–184,
PDF pp. 214–215; 2024 corrections p. 29). The intended application is the
every-point comparison of KP 9.6.6 (printed p. 367, PDF p. 398). All actual
geometric inputs to that application remain obligations of its construction.
The common-apartment argument is an internal consequence of the existing
`AbstractBuilding.IsBuilding` definition and
`PolysimplicialRealization.apartmentComplex`; the facet argument uses the
existing sign-based definition of `AffineRootSystem.IsFacet`. These
conditional constructions do not assemble the five unconditional witnesses
of `RootValuationBuildingConstructionStatement`.
