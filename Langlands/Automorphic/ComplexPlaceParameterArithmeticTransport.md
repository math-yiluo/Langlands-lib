# Arithmetic transport of complex-place parameters

Module `Langlands.Automorphic.ComplexPlaceParameterArithmeticTransport`
(namespace `Langlands.Automorphic.ComplexPlaceArithmeticTransport`). Definitions and proved
lemmas; no statement is left open.

## Orientation of a complex place

Let `e : K ≃+* L` be an isomorphism of number fields and `w` a complex place of `L`. The
corresponding complex place of `K` is `complexPlace e w = w ∘ e`
(`Langlands.Global.ArchimedeanCompactTransport.complexPlace`). Each complex place carries a
selected embedding `embedding`, which identifies its completion with `ℂ`. The embeddings
`w.embedding ∘ e` and `(w ∘ e).embedding` define the same place, so they are equal or
complex conjugate.

| Declaration | Content |
| --- | --- |
| `IsAligned e w` | `w.embedding ∘ e = (complexPlace e w).embedding` |
| `parameter e w d` | the block `d` if `IsAligned e w`, else `d.conj` |
| `parameterList e w ds` | the list `ds` if `IsAligned e w`, else `ds.map ComplexCharacterData.conj` |
| `extensionEmbedding_infiniteCompletionMap_of_isAligned`, `..._of_not_isAligned` | the completed transport `infiniteCompletionMap e w` is the identity of `ℂ` in the selected coordinates when `IsAligned e w`, and complex conjugation otherwise |
| `ringEquiv_mixedSpace_infiniteAdeleEquiv_snd`, `mixedEquiv_snd`, `mixedEquiv_fst` | the resulting formulas for the mixed (real/complex) coordinates of transported infinite adeles |

The dichotomy itself is `ArchimedeanCompactTransport.extensionEmbedding_infiniteCompletionMap`.
The lemmas here decide which case occurs. Evaluated on `K`, the identity case says
`w.embedding ∘ e = (w ∘ e).embedding`. In the conjugate case this equality would make the
embedding real, contradicting that the place is complex.

## Compact and Lie actions at a complex place

| Declaration | Content |
| --- | --- |
| `placeUnitary n e w k`, `compactEquiv_complexPlaceCompactInclusion` | `ArchimedeanCompactTransport.compactEquiv n e` sends the unitary matrix `k` at `w ∘ e` to the unitary matrix at `w` equal to `k` or to its entrywise conjugate |
| `placeMatrix n e w X`, `realLieEquiv_complexPlaceLieInclusion`, `complexLieEquiv_complexPlaceComplexLieInclusion` | `ArchimedeanLieTransport.realLieEquiv n e` (and its complexification) sends the real direction `X` at `w ∘ e` to the direction at `w` equal to `X` or to its entrywise conjugate |
| `complexPlaceCompactRepresentation_arithmeticComapEquiv`, `complexPlaceLieAction_arithmeticComapEquiv` | for an actual operator realization `S` over `L`, the compact and Lie actions at `w ∘ e` on `S.arithmeticComap e` correspond under `S.arithmeticComapEquiv e` to the actions at `w` on `S`, through `placeUnitary` and `placeMatrix` |

The proofs compare coordinates. An element of the infinite adelic `GL_n` is determined by its
`archimedeanGLCoordinates`. The coordinates of the single-place inclusions are given by
`realMatrix_complexPlaceCompactInclusion` and `complexMatrix_complexPlaceCompactInclusion`, and
those of the Lie inclusions by `realProjection_complexInclusion` and
`complexProjection_complexInclusion`. At a place `w' ≠ w` the corresponding place of `K` is
not `w ∘ e` (`complexPlace_injective`), and the entries there are those of `1` or `0`, which
conjugation fixes. The action statements then follow from
`OperatorRealization.arithmeticComapEquiv_compact`,
`OperatorRealization.arithmeticComapEquiv_differential` and
`ArchimedeanLieTransport.envelopingEquiv_generator`.

## Parameters of arithmetic pullbacks

- `hasComplexPlaceParameter_arithmeticComap`: if `S.HasComplexPlaceParameter w ds`, then
  `(S.arithmeticComap e).HasComplexPlaceParameter (complexPlace e w) (parameterList e w ds)`.
  `cuspidal_hasComplexPlaceParameter_arithmeticComap` is the same for actual cuspidal
  realizations and their classes, with `CuspidalOperatorRealization.arithmeticComap`.

  The witness is the actual one. Let `A` be the injective `(𝔤, K)`-map from the `U(n)`-finite
  functions of the standard module of `ds` into `S`. In the aligned case the new witness is
  `A` followed by `S.arithmeticComapEquiv e`. The compact and Lie conditions are those of `A`,
  moved by the two action lemmas above. In the other case the new witness is
  `f ↦ S.arithmeticComapEquiv e (A (f ∘ c))` on the `U(n)`-finite functions of the standard
  module of `ds.map conj`, where `c` is entrywise conjugation of `GL_n(ℂ)`
  (`Langlands.Representation.Archimedean.ComplexStandardModuleConjugation`). Precomposition
  with `c` carries `R(k)` to `R(c k)` and `R(X)` to `R(conj X)`, which are exactly the
  conjugations produced by `placeUnitary` and `placeMatrix`. The length condition is
  unchanged.

- `hasComplexPlaceParameter_comap`: if the Hecke character `χ` of `L` has the parameter `d` at
  `w` (`HeckeCharacter.HasComplexPlaceParameter`), then `HeckeCharacter.comap e χ` has the
  parameter `parameter e w d` at `w ∘ e`. The proof uses
  `HeckeCharacter.comap_infiniteComponent` and the identity-or-conjugation formula for the
  completed transport. `(ComplexCharacterData.conj d).character` is
  `d.character ∘ complexConjugation`.

## Induced parameter lists along compatible isomorphisms

Let `K₁ → L₁` and `K₂ → L₂` be extensions of number fields and `e : K₁ ≃+* K₂`,
`e' : L₁ ≃+* L₂` isomorphisms with `e' ∘ algebraMap = algebraMap ∘ e`. Let `v` be a complex
place of `K₁`.

- `placesAboveEquiv e e' he v`: `w ↦ w ∘ e'⁻¹` is a bijection from the places of `L₁` above
  `v` onto the places of `L₂` above `v ∘ e⁻¹`.
- `isAligned_iff_iff`: four identity-or-conjugation choices occur. They are reading at `v`
  along `e⁻¹` (`IsAligned e.symm v`), from a place `w` above `v` to `v` (as in
  `complexPlaceParameterTransport`), from the corresponding place `w ∘ e'⁻¹` to `v ∘ e⁻¹`,
  and at `w` along `e'⁻¹`. Their parities agree: `(a₁ ↔ a₂) ↔ (a₃ ↔ a₄)`. Proof: compose
  every embedding to an embedding of `K₂` defining `v ∘ e⁻¹`. Each such embedding is the
  selected one `U` or its conjugate, and `U ≠ conj U` because the place is complex. Each
  condition becomes an equality between two of these embeddings. Composing with
  `algebraMap K₂ L₂` loses no information here, because a conjugate of a non-real embedding
  differs from it.
- `parameterList_complexPlaceParameterTransport` (one block) and
  `parameterList_complexPlaceLanglandsSum`: for any enumeration `en` of the places above `v`
  and blocks `dξ`,
  `parameterList e.symm v (complexPlaceLanglandsSum v en fun w => [dξ w])` equals
  `complexPlaceLanglandsSum (v ∘ e⁻¹) (en.trans (placesAboveEquiv e e' he v)) (fun w₂ => [dχ w₂])`.
  Here `dχ w₂ = parameter e'.symm (complexPlaceAbove v w) (dξ w)` for the place `w` above `v`
  corresponding to `w₂`. `perm_parameterList` and `parameterList_flatten_ofFn` are the list
  facts used.

## Provenance

Derived content. Over `ℂ` the only continuous field automorphisms are the identity and
complex conjugation (`Complex.ringHom_eq_id_or_conj_of_continuous`). An isomorphism of
number fields therefore acts on the archimedean component of an automorphic representation
at a complex place either trivially or by conjugation in the selected coordinates.
Conjugation acts on Langlands parameters by conjugating the characters. This is the
archimedean part of the transport of automorphic representations and Hecke characters along
field isomorphisms. It uses the Library's archimedean witness `HasComplexPlaceParameter`
(`Langlands.Automorphic.ArchimedeanPlaceParameter`) and the Langlands sums
`complexPlaceLanglandsSum` (`Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport`).
It is used for Harris (1998), Proposition 4.8, in
`Langlands.Global.Arithmetic.HarrisProposition48MackeyChildTransportProof`.
