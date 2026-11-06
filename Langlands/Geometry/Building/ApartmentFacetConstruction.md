# Apartment embeddings and facet compatibility for the actual quotient

This internal construction concerns supplied `ValuationBuildingData G` over an
arbitrary nonarchimedean local field at every universe `u`. It retains the full
`B.SatisfiesApartmentAxioms` predicate, including AS5. Apartment-map injectivity
and the assembled AS6 witness also retain
`RelativeRoot.HasRankOneFactorization B.i`, the actual opposite-factor-pair
condition. The group, actual maximal split torus, root filtration, apartment,
quotient, and rational-point action are the original objects of `B`.

The module proves `B.HasCompatibleApartmentFacets`: the original apartment map
is injective and every building facet meeting its image is the image of an
apartment facet. The entry `translatedApartmentChartOfRankOne` packages the
original translated chart `x ↦ g • B.apartmentMap x` as an equivalence onto the
same translated apartment subset. Its application theorem records this exact
underlying value. This is an equivalence of types, without a new affine or
topological structure on that subset.

## Implemented proof

The published `PointParahoricNormalizer` theorem proves that a normalizer point
in the singleton sharp fixer fixes that apartment point, under the displayed
apartment and opposite-factor-pair premises. Applying the existing
`ApartmentQuotient.apartment_injective` criterion gives injectivity of
`B.apartmentMap`.

For facet compatibility, start with a translate by `g` of an apartment facet
`Fa`, with `a ∈ Fa` and `g • apartmentMap a = apartmentMap b`. The defining
quotient relation supplies `n ∈ N(F)` with `n • a = b` and
`p = g⁻¹ n ∈ sharpFixer {a}`. The published AS4 facet constancy theorem gives
`p ∈ sharpFixer Fa`, so `p` fixes `apartmentMap y` for every `y ∈ Fa`.
Multiplying this equality by `g` proves
`g • apartmentMap y = apartmentMap (n • y)` on the entire facet.

The AS5 inclusion puts the affine action of `n` in the extended affine Weyl
group, hence in the affine-root stabilizer. The existing `image_facet` theorem
then says `n • Fa` is an apartment facet. The displayed equality on `Fa`
identifies the given translated facet exactly with
`apartmentMap '' (n • Fa)`. This part needs the apartment axioms alone, without
opposite factor pairs, injectivity, or the apartment-stabilizer equality.

The two conclusions are the two fields of the unchanged AS6 predicate.
Finally, `translatedApartmentChartOfRankOne` uses the derived injectivity in the
published translated-chart construction.

## Provenance and scope

This is a deduction from current Library definitions and proved interfaces,
principally `PointParahoricNormalizer`, `ChamberParahoricConstancy`,
`ApartmentQuotient`, `IwahoriWeylChamberLemmas`, and
`ValuationBuildingApartmentCharts`. It introduces no external source assertion.
The AS6 label refers to the existing Library predicate for the apartment clause
of KP Axiom 4.1.6; no additional part of that axiom is asserted here.

General existence of the supplied valuation data, the apartment axioms
themselves, actual opposite factor pairs, and the other witnesses in
`RootValuationBuildingConstructionStatement` remain obligations. In particular,
AS5 has not been discharged by this construction.
