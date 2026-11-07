import Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement
import Langlands.Automorphic.CuspidalWhittaker.LocalFunctional
import Langlands.Automorphic.LocalWhittakerCharacterBridge

/-!
# Actual local genericity of cuspidal presentations

Every irreducible admissible local component of a spectral presentation of a cuspidal
realization is generic for every nontrivial unitary additive character of the local field.
The global Whittaker coefficient gives a nonzero functional on the local component that is
equivariant for the local component of the standard character of `𝔸_K / K`; that character is
trivial on the local integers and nontrivial, so the character-change bridge applies.
-/

noncomputable section

universe uF uQ

namespace Langlands.Automorphic

open Langlands.Global

/-- **Local genericity** of the actual local components of cuspidal spectral presentations. -/
theorem cuspidalUnitaryLocalGenericity : CuspidalUnitaryLocalGenericityStatement.{uF, uQ} := by
  intro F _ _ _ r T _ P v hI hA
  have hne : CuspidalWhittaker.localCharacter F v ≠ 1 := by
    intro h
    obtain ⟨t, ht⟩ := CuspidalWhittaker.exists_localCharacter_ne_one F v
    exact ht (by rw [h, AddChar.one_apply])
  obtain ⟨ℓ, hℓ, heq⟩ := CuspidalWhittaker.exists_localWhittakerFunctional (P.localComponent v)
    (P.localComponent_isCuspidal v) (P.localComponent_ne_bot v)
  exact (P.localComponent v).isGeneric_of_integerTrivial_character hI hA
    (CuspidalWhittaker.localCharacter F v) hne
    (fun _ hx => CuspidalWhittaker.localCharacter_eq_one F hx) ℓ hℓ heq

end Langlands.Automorphic
