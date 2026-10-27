# Actual graded comparison for character-localized image filtrations

`Langlands.Jacquet.Localization.imageFiltrationGraded` proves the exact
proposition `Langlands.Jacquet.Localization.ImageFiltrationGradedStatement`.
It constructs the actual image filtration of a smooth complex representation
under character localization and identifies every actual graded quotient
equivariantly with the localization of the corresponding original quotient.

The hypotheses are those of the published statement: an arbitrary topological
group `G`, a subgroup `U` satisfying `IsLimitOfCompactSubgroups U`, a locally
constant complex-unit character `θ` of `U`, a subgroup `M` normalizing `U` and
preserving `θ`, and a smooth actual representation with a finite invariant
zero-to-full filtration. No further premise is used.

The proof uses the actual image of every supplied invariant step to construct
the output filtration, with the original order and endpoints. Localizing the
inclusion of a step into the smooth ambient representation gives an injective
equivariant map. Its range is exactly that image step: surjectivity of the
character quotient map supplies representatives. Restricting the codomain
therefore gives an equivalence from the localization of the step to its image.

The actual adjacent inclusion and graded projection form an exact sequence.
Character-localization exactness identifies the range of the localized
inclusion with the kernel of the localized graded projection and preserves
surjectivity of that projection. Injectivity of the localized inclusion into
the ambient representation shows that this kernel corresponds precisely to
the lower image step. Transporting the projection through the upper-step
equivalence and applying the equivariant first isomorphism theorem gives the
actual graded equivalence.

The implementation constructs the output with
`ObjectRepFiltration.ofSubrepresentations`, using the published image
monotonicity and endpoint lemmas. `stepImageEquiv` gives the upper-step
equivalence; `localized_adjacent_kernel` proves the required kernel equality.
The final quotient equivalence uses
`MultiplicityAdditivityProof.quotient_equiv_of_surjective`, the published
equivariant first isomorphism theorem.

This is an internal algebraic consequence of the published localization and
filtration constructions and `LocalizationExactnessProof`. No separate literal
literature assertion is attributed. The theorem preserves independent group
and carrier universes `uG` and `uV` and includes zero filtration length,
repeated steps and zero representations. No finite-dimensionality,
admissibility, finite composition length, splitting or semisimplicity
hypothesis is added. This objectwise character-localization result supplies a
prerequisite for subsequent Jacquet arguments; it asserts no normalized
Jacquet comparison, categorical naturality, multiplicity formula or
irreducible-head theorem.
