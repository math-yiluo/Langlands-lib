import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport

/-! # Reversing complex-place parameter transport

An elementary consequence of the selected-coordinate identity/conjugation formula.
This does not assert compatibility of automorphic representations.
-/

noncomputable section

universe uF uE

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global.AdelicFunctoriality Langlands.LocalFactor.Archimedean

private theorem complexCharacterData_conj_conj (d : ComplexCharacterData) :
    d.conj.conj = d := by
  cases d with
  | mk character weight exponent character_eq =>
    have hcharacter :
        (character.comp complexConjugation).comp complexConjugation = character := by
      ext z
      change (character (complexConjugation (complexConjugation z)) : ℂ) = (character z : ℂ)
      have hz : complexConjugation (complexConjugation z) = z := by
        apply Units.ext
        change star (star (z : ℂ)) = (z : ℂ)
        exact star_star _
      rw [hz]
    simp only [ComplexCharacterData.conj, neg_neg, hcharacter]

/-- The same identity/conjugation operation transports parameter lists in either
direction between the selected coordinates at a complex place and a place above it. -/
theorem complexPlaceParameterTransport_involutive
    {F : Type uF} {E : Type uE} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E]
    (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    (w : InfinitePlacesAbove E v.1) :
    Function.Involutive (complexPlaceParameterTransport v w) := by
  classical
  intro ds
  by_cases h : w.1.embedding.comp (algebraMap F E) = v.1.embedding
  · simp only [complexPlaceParameterTransport, h, ↓reduceIte]
  · simpa only [complexPlaceParameterTransport, h, ↓reduceIte] using
      (List.map_involutive_iff.mpr complexCharacterData_conj_conj) ds

end Langlands.Automorphic.Unramified
