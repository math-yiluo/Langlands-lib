# Determinants of Brauer relations and additive-character independence

Author: Worker 1838. This module is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. It proves
no part of that statement's arithmetic identity. It shows that the identity does
not depend on the chosen nontrivial additive character. This is the
presentation-level counterpart of Deligne (1973), Lemma 4.3, printed page 536
(PDF page 36): `ε(v, ψ(ax)) = det(v)(a) ε(v, ψ)` for virtual monomial
representations `v` of degree zero.

All objects are the unchanged ones from `NonabelianBrauerPresentation`: the
generators `Generator F E`, the free module `Presentation F E`, the actual
induced classes `generatorClass` and `virtualPresentation`, the codomain-restricted
`presentationMap`, and the epsilon-ratio evaluation `evaluationMap`.
The field universe `uF` and the representation universe `uV` remain independent.

## Determinant of a generator

`generatorCharacterRatio F E g a` is the unit `χ(a) / χ'(a)`. Here `χ` and `χ'` are
the two characters of the generator `g` on its field `L`, and `a ∈ Eˣ` is mapped
into `Lˣ` by the actual field inclusion.

The imported `determinant_generatorClass` from `NonabelianBrauerScaling` computes the actual exact-virtual
determinant of `generatorClass F e E g` at a Weil element `w`: it is the
character ratio at the reciprocity image of `w`. The proof applies the published
`determinant_induce_degreeZero_reciprocity` to the degree-zero class
`[χ] - [χ']` on `L`. Its Gallagher hypothesis is discharged by the published
theorem `LocalFactor.Inductive.gallagherDeterminant`. A compatible Weil lift on
`L` comes from `exists_reciprocityUnits_eq`. The determinant of each character
line is the line's Weil character (`CommonClosure.determinantCharacter_characterClass`),
and the Weil character evaluates the field character at the reciprocity image.
The normalized-reciprocity premise is used only through the transfer/inclusion
square inside the published determinant theorem.

## Relations have trivial character-ratio product

`characterRatioMap F E a` is the integer-linear extension of
`g ↦ generatorCharacterRatio F E g a` into `Additive ℂˣ`. As for `evaluationMap`,
zero is the complex unit one and addition is multiplication.
`characterRatioMap_eq_determinant` identifies it with the determinant of
`virtualPresentation F e E z` at any Weil element whose reciprocity image is `a`.
The proof is induction over finitely supported functions, using additivity and
integer-power compatibility of the exact determinant.

`characterRatioMap_eq_zero` follows. If `presentationMap F e E z = 0`, then the
virtual class is zero, and its determinant is the trivial character. Every unit
of `E` has a Weil lift, so the product
`∏_g (χ_g(a)/χ'_g(a))^{z(g)}` is one for every `a ∈ Eˣ`.

## Scaling the additive character

In namespace `Langlands.PadicField.TopologicalData`, for any supplied
topological datum `T`, the first two lemmas are reused from
`NonabelianBrauerScaling`:

- `abelianEpsilonUnit_scale`: `ε(χ, ψ(a·), μ)` equals
  `abelianScalingFactor χ a · ε(χ, ψ, μ)` as complex units. This is the published
  `abelianEpsilonExpression_scale_factor` lifted along `Units.ext`.
- `abelianEpsilonRatio_scale`: for the ratio of two characters with the same `ψ`
  and `μ`, the scaling factors leave only `χ(a)/χ'(a)`. The common factor
  `|a|⁻¹` cancels.
- `isLocallyConstant_additiveCharacter`: every continuous unitary additive
  character is locally constant, since it is trivial on some additive lattice
  (`exists_additiveTrivialAt`), and additive lattices are open.
- `exists_scale_eq`: every nontrivial continuous unitary additive character `ψ'`
  equals `ψ.scale a` for some unit `a`. The published
  `exists_eq_complex_mul_of_isLocallyConstant` gives `a`. Here `a ≠ 0`, since
  otherwise `ψ'` would be trivial.

The presentation calculation reuses the existing scaling lemmas:

- `CommonClosure.traceCharacter_scale` (from `NonabelianTraceScaling`): pulling `ψ(a·)` back by the trace gives the trace
  pullback of `ψ` scaled by the image of `a`. This uses
  `Tr_{L/E}(a x) = a Tr_{L/E}(x)`.
- The imported `generatorValue_scale` and the new `evaluationMap_scale_characterRatio`: scaling `ψ` by `a` multiplies
  each generator value by its character ratio. On presentations, it adds
  `characterRatioMap F E a`.
- The imported `evaluationMap_scale_of_presentationMap_eq_zero`: on an actual relation the evaluation is
  unchanged by scaling.
- `evaluationMap_additiveCharacter_independent`: on an actual relation the
  evaluation is the same for any two nontrivial additive characters of `E`.

The existing `evaluationMap_scale` remains the linear-map identity with a
normalized reciprocity family and a Weil lift. The new
`evaluationMap_scale_characterRatio` is pointwise and requires neither input.
Both interfaces retain their original hypotheses and conclusions.

The Haar family is arbitrary throughout and is never changed.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`. Lemma 4.3 (printed page 536, PDF
page 36) proves the corresponding identity on Deligne's monomial group from
Gallagher's formula 1.2 and the identification of the field inclusion with the
transfer. The present module is an internal derivation of that argument on the
Library's free presentation of the continuous exact common-closure group. All
analytic and arithmetic inputs are published theorems named above.
