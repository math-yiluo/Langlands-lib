# Recovered residue maps on a maximal-unramified fixed facet

This is an internal prerequisite for the fixed-point split-torus construction.
It proves actual component-model recovery at a supplied original Galois-fixed
facet and coefficient naturality for every residue morphism recovered from the
original residue field. The proposition
`KPApartmentData.UnramifiedFixedFacetRecoveredMapsStatement` and theorem
`unramifiedFixedFacetRecoveredMaps` package these conclusions. They are
universe-polymorphic and impose no characteristic restriction.

The supplied data are the local field `F`, an apartment datum over its maximal
unramified extension with Galois stability, the connected reductive generic group
and maximal split torus there, the centralizer and compatibility data, and an
actual integer facet-model family `M`. Its full integral points must be the
intersection of the character valuation kernel with the pointwise facet fixer.
The selected facet `E` is an original Galois facet. Geometric connectedness of
the generic group over `F` is an explicit hypothesis of the existence assertion.

The conclusion constructs an actual relative-component model `N0` over the
integers of `F` and an `UnramifiedComponentModelRecovery` of the component model
at `E`. For every original-residue group scheme `H` and actual map
`q : N0.neutral.specialFibre ⟶ H`, recovery yields a map from the neutral special
fibre at `E` to the residue extension of `H`. The original fixed-facet residue
comparison, followed by this map, equals the residue coefficient pullback of
this map followed by the canonical descent comparison of `H`. This is a literal
group-scheme morphism equality; it is not an assumption on point sets.

## Integral and residue transport

`IntegralModel.Iso.changeTarget` closes an actual integral comparison along an
equality of its target model. The two `residueTwistIso_changeTarget` lemmas show
that specialization performs exactly the corresponding equality transport on
the original special fibre. `residueTwistIso_congr` shows that residue
specialization depends on the actual integral isomorphism and not on the chosen
presentation of its generic compatibility.

Over abstract coefficient fields and integers,
`fixedFacetNeutralGaloisIso` closes the published neutral coefficient comparison
using the proved equality between the translated facet and the original fixed
facet. `fixedFacetNeutralGaloisIso_residue` identifies its specialization with
the published `fixedFacetResidueGaloisIso`. For any actual downstairs neutral
model recovery and residue map, `fixedFacetResidueDescendedMap_naturality` applies
`IntegralModel.residueDescendedMap_naturality`. The equality
`galoisDescentIso_def` aligns the generic comparison with canonical coefficient
descent; the residue congruence lemma and specialization identity then recover
the original fixed-facet comparison.

## Canonical unramified specialization

`fixedIntegerBaseAut_over` proves on integer elements that the coefficient
automorphism fixes the original integers, using `σ.commutes`.
`fixedResidueBaseMap_square` proves the actual integer/residue coefficient square
using `residueToFixedField_residue`. Together with the published generic and
residue automorphism squares, these discharge every coefficient hypothesis in
the abstract naturality result. The resulting constructions are
`unramifiedFixedFacetNeutralIso`, `unramifiedFixedFacetDescendedMap`, and their
specialization and naturality theorems.

`exists_unramifiedFixedFacetRecovery` uses the published theorem
`IntegralModel.unramifiedSmoothModelDescent` through
`exists_unramified_componentModelRecovery`. The full-model integral points are
Galois-stable by `full_integralPoints_galois_iff` and the proved fixed-facet
equality. The final theorem chooses that recovery and applies canonical
naturality to every original-residue map.

## Provenance and remaining scope

The construction is derived from the published modules
`UnramifiedFacetResidueComparisons`, `RecoveredResidueDescent`,
`UnramifiedNeutralModelDescent`, and `UnramifiedSmoothDescentProof`. No external
source is claimed for this categorical and arithmetic specialization. The
residue maps are actual supplied morphisms from the recovered downstairs
neutral special fibre. This module does not construct a reductive quotient, an
identification of an upstairs quotient with a downstairs quotient, a
facet-parabolic correspondence, a residue torus or its lift, or the
fixed-point split torus of `UnramifiedFixedPointSplitTorusStatement`. These remain separate geometric steps.
