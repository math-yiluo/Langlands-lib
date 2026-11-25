# Complex-place parameters of norm pullbacks

Module `Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm`, namespace
`Langlands.Automorphic.Unramified`. Internal helper
results; no source is cited.

Let `K ⊆ L` be number fields (`Algebra K L`), `v` a complex place of `K` and `w` a place of
`L` above `v` (`InfinitePlacesAbove L v`). The Library reads a complex place in the selected
coordinate `extensionEmbedding`; `complexPlaceParameterTransport v w` (module
`ComplexPlaceParameterTransport`) passes between the coordinates of `v` and `w` by the
identity when `w.embedding ∘ algebraMap K L = v.embedding`, and by conjugating every block
otherwise.

## Character data

In namespace `ComplexCharacterDataLemmas`: `ext` (equal character, weight and exponent give
equal data), `complexConjugation_complexConjugation`, `conj_conj` (conjugation is an
involution) and `conj_mul` (conjugation commutes with the published `ComplexCharacterData.mul`).

## The local norm

- `extensionEmbedding_completionMap_of_comp_eq` / `_of_comp_ne`: in the selected coordinates
  the completion map `K_v → L_w` is the identity when `w.embedding` restricts to
  `v.embedding`, and complex conjugation otherwise. These come from Mathlib's
  `liesOver_extensionEmbedding`, `liesOver_conjugate_extensionEmbedding` and
  `LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq`.
- `isUnramified_of_isComplex`: a place above a complex place is unramified, so
  `[L_w : K_v] = 1` (Mathlib's `IsUnramified.finrank_eq_one`).
- `extensionEmbedding_localNorm`: the published local norm
  `InfiniteExtension.localNorm v w` (the algebra norm `L_w → K_v`) is, in the selected
  coordinates, the identity in the first case and complex conjugation in the second. Every
  element of `L_w` is the image of an element `y` of `K_v` (by the previous coordinate
  formula), and its norm is `y ^ [L_w : K_v] = y` (published `localNorm_algebraMap`).
- `ideleNorm_infiniteIdeleInclusion`: the published idele norm sends the idele equal to `x` at
  `w` and `1` elsewhere to the idele equal to `localNorm v w x` at `v` and `1` elsewhere. At
  `v` the product over the places above `v` has the single nontrivial factor at `w`; at every
  other place `p` no place above `p` equals `w`; the finite part is `1`.

## Parameters

- `normParameter v w e` is `e` in the first case and the conjugate `ē` in the second.
- `hasComplexPlaceParameter_comp_ideleClassNorm`: if the Hecke character `μ` of `K` has the
  parameter `d` at `v`, then `μ ∘ N_{L/K}` (composition with the published `ideleClassNorm`)
  has the parameter `normParameter v w d` at the place `w` (as the complex place
  `complexPlaceAbove v w`).
- `complexPlaceParameterTransport_map_mul`: multiplying the transported singleton `[a]` by `e`
  gives the transport of `[a.mul (normParameter v w e)]`; in the conjugate case this uses
  `conj_mul` and `conj_conj`.
- `complexPlaceLanglandsSum_map_mul`: multiplying every block of the published
  `complexPlaceLanglandsSum v en (fun w => [a w])` by `e` gives
  `complexPlaceLanglandsSum v en (fun w => [(a w).mul (normParameter v w e)])`, with the same
  enumeration `en`.
