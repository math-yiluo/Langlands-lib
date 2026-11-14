# Common maximal split tori and Lie-weight signs for descended facet models

The theorem `Langlands.BruhatTits.IntegralModels.unramifiedFacetCommonTorus`
proves the unchanged Library proposition
`UnramifiedFacetCommonTorusStatement.{u}` at arbitrary universe `u`.
It concludes maximality of the supplied integral torus in the target special
fibre and its reductive quotient, together with the apartment Lie-weight sign
formula for each split-torus witness. This is the published formulation of
KP Axiom 4.1.22(3) on the supplied descended models.

The proof introduces every input of that proposition: the seven building
hypotheses, the eight apartment-descent hypotheses, the incident apartment
facets and their translated presentations, and every characterized model
pair, model morphism, reductive quotient and integral torus satisfying the
torus clause. Both model smoothness hypotheses remain quantified.
The statement and the declarations it imports are unchanged.

`RelativeComponentModelHom.hasMaximalSplitTori_integer` gives maximality
for the same supplied torus in the target special fibre and reductive
quotient. Its source-special-fibre maximality comes from the torus-clause
hypothesis. The proof selects the two requested target conjuncts.

For each split-torus witness, the proof applies
`unramifiedFacetLieWeightSignFormula_of_descent` with the unconditional
proofs `unramifiedFacetLieWeightSign` and
`Langlands.Geometry.Building.unramifiedDescendedApartmentTorus`.
The first supplies the weight-sign equality over the maximal unramified
extension; the second supplies the torus inclusion used in descent.
The descent theorem receives all of the original building, apartment,
facet and model data and yields precisely the required
`HasApartmentLieWeightSignFormula`.

The implemented proof is a composition of these Library interfaces. It
introduces no additional premise, chosen-model restriction or replacement
for the supplied torus. Its provenance is this internal composition; the
source correspondence of the target is documented in the unchanged
`UnramifiedFacetCommonTorusStatement.md`.
