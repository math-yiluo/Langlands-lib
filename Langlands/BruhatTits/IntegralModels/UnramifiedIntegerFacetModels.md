# Constructed actual models and parabolic correspondence on all integer facets

Module `Langlands.BruhatTits.IntegralModels.UnramifiedIntegerFacetModels`.
This internal construction works at arbitrary universe `u` and in both
characteristics.

Let `F` be a nonarchimedean local field, `G` an affine group scheme over
`inertiaFixedField F`, `E : UnramifiedZeroDatum F G` any actual zero datum,
and `C : MaximalUnramified.BuildingData F G` supplied building data. The
building data include connected reductivity, a maximal split torus, the
actual apartment and centralizer, and full omega compatibility.

`UnramifiedIntegerFacetModelsStatement` constructs one actual
`IntegerFacetModelData C (fixedFieldIntegers F)` with both exact formulas
at every original full facet `J`: its full integral-point subgroup is the
rational-character valuation kernel intersected with the pointwise fixer
of `J.val`, and its neutral integral-point subgroup is `E.zeroPoints`
intersected with that same fixer. For every facet and every valid supplied
reductive quotient of its neutral special fibre, this same family's actual
incident-image map has the full existing facet-parabolic order bijection.
`unramifiedIntegerFacetModelsStatement` proves this Prop-valued statement.
No model family, model morphisms, integral-point formulas or geometric
image-bijection hypotheses are assumed.

## Implemented construction

The private `integerFacetModel_torusInputs` composes published arithmetic
proofs. `connectedGeneration` discharges the connected-generation premise
of `unramifiedTorusNeutralSurjectivityAssembly`; the other inputs are
`torusQuotientRationalSurjectivity`, `unramifiedTorusNeutralFiniteGeneration`
and `torusSurjectionIsogenySection`. Then
`unramifiedTorusConnectedBoundAssembly`, with `unramifiedTorusBoundedModel`
and `unramifiedTorusNormPresentation`, gives the connected torus bound.
`unramifiedTorusIwahoriModelAssembly` combines this bound with the proved
smooth extension criterion, maximal-bounded torus model construction and
`unramifiedTorusIwahoriConnectedImage` to supply the torus Iwahori models.
These are proved inputs, not extra universal hypotheses.

`exists_unramifiedIntegerBuildingFacetModel` presents any full facet in a
translated original apartment. The apartment facet is nonempty and bounded:
`MaximalUnramified.exists_order_eq_one` supplies a nonzero-order unit, and
`isBoundedApartmentSubset_of_isFacet` bounds every real affine functional
on that facet. The published
`exists_unramifiedParahoricModel_of_torusInputs` then supplies an actual
smooth full model and its actual relative identity component, with both
exact generic-point subgroup formulas for this same `E` and translated
facet. This use of the generic constructor does not assume that the
maximal unramified field is itself a nonarchimedean local field.

`unramifiedIntegerBuildingFacetModel` chooses such a model for each full
facet; its two field lemmas preserve the two formulas. The constructed
`unramifiedIntegerFacetModels` uses the published
`IntegerFacetModelData.ofIntegralPoints` to obtain actual full incidence
maps and their neutral restrictions from inclusion of the full generic
integral-point images. This uses the proved smooth-extension theorem over
the strictly Henselian DVR `fixedFieldIntegers F`. No incidence comparison
is supplied independently.

Finally `unramifiedIntegerFacetModels_hasFacetParabolicOrderBijection`
applies the proved full integer-facet correspondence to the constructed
family's neutral formula. Parabolic attainment, image injectivity, target
congruence containment and actual special-fibre parabolicity were proved
there from the published root-generation and actual-image geometry.
The quotient remains any supplied valid quotient; this module does not
choose quotients or a residue descent comparison.

The import route uses the separately staged generic root-fixer cleanup
and generic torus-adapter relocation; no prohibited building-descent
statement is a proof input. This constructs the actual model family and
its geometric residue correspondence, while the host fixed-point
split-torus theorem still requires the Galois and torus-lifting arguments.
