# Actual residue coefficient comparisons at a Gamma-facet

This internal derived unit constructs the source and target residue isomorphisms
at an actual Galois-fixed facet from the full integral-point description of
supplied integer-facet models. Its public proposition is
`Langlands.Geometry.Building.KPApartmentData.GaloisFacetResidueComparisonsStatement`.
It works in arbitrary universe and both characteristics over a strictly Henselian
discrete valuation ring with separably closed residue field.

The inputs are the actual apartment and integer-building data, an actual
Galois-fixed facet, a family of integer-facet models, their exact full
integral-point images as the intersection of the character-valuation kernel
with the original pointwise facet fixer, valuation covariance, invertible
integral coefficient maps with generic squares, a residue coefficient action
with residue squares, a quotient and its comparison with a base-changed
residue group. These conditions have precisely their Lean meanings. The
quotient is not required to be reductive for the comparisons in this unit.

`incidentResidueGaloisIso` specializes the constructed comparisons of
`GaloisFacetModelComparisons` to the actual underlying facet of the incident
Galois action. `fixedFacetResidueGaloisIso` composes the same comparison at the
fixed facet with equality transport along
`galoisBuildingFacetAction_galoisFacet`. The incidence square follows from
`neutralResidueGaloisIso_naturality`: associativity moves the equality
transport onto the incidence map, where a private dependent transport lemma
identifies it with the actual incidence map. No source or target isomorphism
or incidence square is assumed.

`FixedFacetResidueQuotientSquare` records the remaining literal quotient square
using this constructed target isomorphism. Supplying it constructs
`ResidueCoefficientComparisonData` via
`residueCoefficientComparisonsOfQuotientSquare`. The all-test image covariance
then follows from
`hasGaloisResidueImageCompatibility_of_coefficientComparisons` in
`GaloisFacetImageNaturality`. The final theorem combines the existence of this
actual comparison data and the resulting covariance.

This is an internal construction from the named Lean inputs, not a claim of
an additional theorem from the literature. Existence of the models, their
full point descriptions, the compatible coefficient maps, the quotient square,
the actual facet-parabolic bijection, torus lifting, segment comparison and
the unconditional fixed-point split-torus theorem remain separate obligations.
