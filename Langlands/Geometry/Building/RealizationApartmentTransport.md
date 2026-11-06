# Apartment order isomorphisms on a supplied realization

Let `B : ValuationBuildingData G` be supplied actual data over a
nonarchimedean local field at arbitrary universe `u`, and let
`R : B.PolysimplicialRealization` be supplied. The constructions below use the
original quotient, rational-point action, facets and incidence relation.
`R.IsFaceCompatible` remains an explicit premise: inclusion of complex facets
is equivalent to the existing `FacetPrecedes B` on their realizations.

## Transporting the facet order

`R.facetTranslateOrderIso hR g` conjugates the existing facet permutation
`B.facetTranslateEquiv g` by `R.realize`. Face compatibility and the original
action's preservation and reflection of incidence prove that this is an order
isomorphism of `R.complex.facets`, ordered by literal inclusion of complex
facets. `realize_facetTranslateOrderIso` records its exact action on the
realized building facets. This construction is an order isomorphism of facets;
it does not assert that a permutation of the vertex set induces it, and it
does not prove `R.IsPolysimplicialAction`.

`R.apartmentFacetOrderIso Y` identifies `R.apartmentComplex Y` with the subtype
of complex facets whose realized subsets lie in `Y`. Its maps retain exactly
the same underlying complex facet; the existential membership witness supplies
the facet proof and containment. `R.apartmentFacet` and
`apartmentFacet_subset` expose this facet and its containment.

Given `g • Y = Z`, `R.apartmentTranslateOrderIso hR g Y Z hg` restricts the global
facet order isomorphism through these subtype identifications. Realization of
the global map is the actual translated subset, so containment in `Z` is
equivalent to original containment in `Y`, using invertibility of the group
action. `realize_apartmentTranslateOrderIso` gives the exact realized-facet
formula. These constructions work for arbitrary subsets `Y` and `Z` satisfying
the stated equality; no apartment axioms are assumed.

The separate theorem `isSubcomplex_apartmentComplex` assumes the full
`B.SatisfiesApartmentAxioms` predicate and that `Y` is an actual apartment. It
proves the existing `AbstractBuilding.IsSubcomplex` predicate. A lower complex
facet gives a lower building facet by face compatibility; the previously proved
`subset_apartment_of_facetPrecedes` puts that lower facet into the same actual
apartment. Chart injectivity is not needed.

## BL4 from the Tits-system comparison

Now take supplied `P : ParahoricBuildingData G`, a supplied realization of
`P.toValuationBuildingData`, face compatibility, and a witness
`hT : P.IsBuildingTitsSystem Ca π Sgen`. This is the full existing Tits-system
comparison predicate, including the stabilizer bijection, incidence as reverse
stabilizer inclusion, and apartment comparison. It is an assumption here.

`hT.exists_realization_apartmentOrderIso` takes actual apartments `Y` and `Z`
and two complex facets `F₁` and `F₂` whose realized subsets lie in both. The
existing `hT.exists_twoFacet_smul_apartment_eq` provides `k : P.zeroSubgroup`
that carries `Y` to `Z` and belongs to the stabilizers of both realized facets.
The preceding apartment construction gives an order isomorphism between
`R.apartmentComplex Y` and `R.apartmentComplex Z`.

For any complex facet `Fc` in the first apartment with `Fc ⊆ F₁` or
`Fc ⊆ F₂`, face compatibility and `hT.facetPrecedes_iff` put the corresponding
upper-facet stabilizer inside the stabilizer of `R.realize Fc`. Thus the same
`k` fixes that realized facet as a subset. The realization bijection then shows
that the apartment order isomorphism fixes `Fc` itself. This proves the required
fixation of every subface, including the two upper facets by reflexivity; it
uses setwise facet stabilization, without a pointwise-fixation premise.

`hT.realization_exists_orderIso` unpacks the existential description of
`R.apartments` and the membership of each common facet, and applies that result.
Its conclusion is exactly the `exists_orderIso` field of the existing
`AbstractBuilding.IsBuilding` predicate, namely BL4. No full apartment-axiom
or chart-injectivity premise is needed for BL4 once `hT` and face compatibility
are supplied.

## Provenance and scope

This is an internal derived construction from `FullValidity.Realization`,
`BuildingFacetAction`, the apartment-containment lemma of
`BuildingFacetIncidence`, and `TitsFacetApartmentTransport` with its original
Tits-system incidence/stabilizer interface. The proof above describes the
implemented deductions. No new external assertion is introduced.

The module does not construct a polysimplicial realization, prove face
compatibility or the Tits-system comparison, or prove BL1, BL2, BL3 or the
polysimplicial vertex-action clause. General valuation-data existence,
torus/apartment correspondence and the full unconditional
`RootValuationBuildingConstructionStatement` remain open.
