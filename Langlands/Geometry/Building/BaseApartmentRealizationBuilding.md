# Building assembly from one original apartment

This is an internal deduction from `RealizationApartmentTransport`,
`AbstractBuilding` and `AffineTitsRealizationBuilding`. It introduces no external
source assertion. The field, group, valuation quotient, facet realization and
apartments are the existing objects, at every universe `u`.

Let `B` be supplied actual valuation building data and `R` a supplied
face-compatible polysimplicial realization. Every actual apartment is
`g • B.apartmentImage`. The existing `apartmentTranslateOrderIso` restricts
the original rational-point action on facets to an order isomorphism from
the complex of the original apartment onto the complex of this translate.
Transporting an `IsPolysimplicial` witness along that order isomorphism proves
`isPolysimplicial_apartment_of_base`. No apartment axioms, Tits comparison or
injectivity premise is needed for this transport.

`isPolysimplicial_all_apartments_iff` states the resulting equivalence between
polysimpliciality of every actual apartment and polysimpliciality of the
original apartment. The forward implication specializes at the original
apartment, which is itself an apartment by translation by the identity.

`realization_isBuilding_of_base` uses this transport in the general conditional
Tits-system building assembly. It retains the full building Tits comparison,
face compatibility, admissibility of every simple singleton and the one
original-apartment polysimplicial witness.

`affineTitsRealizationBuildingOfBase` instead uses the literal actual affine
Tits datum: its Weyl group is `P.affinePart`, its projection is
`P.affineTitsProjection`, and its simple set is
`P.chamberSimpleInAffinePart e Ca`. The existing affine assembly proves
singleton admissibility from the supplied affine-root-system and actual
chamber hypotheses. The new definition then supplies the universal apartment
premise by translation of the one original-apartment witness.

This module does not construct that witness, the actual valuation data, the
full Tits comparison, the affine-Weyl equivalence or the realization. The
polysimplicial action, torus-apartment correspondence and normalizer-stabilizer
clauses of `SatisfiesBuildingAxiom` remain separate obligations. In particular,
the unchanged unconditional `RootValuationBuildingConstructionStatement`
is not proved here.
