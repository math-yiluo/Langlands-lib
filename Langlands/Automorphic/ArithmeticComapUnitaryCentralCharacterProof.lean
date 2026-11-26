import Langlands.Automorphic.CuspidalArithmeticTransportStatement

/-!
# Arithmetic pullback preserves a unitary central character

For a ring isomorphism `e : K ≃+* L` of number fields and a cuspidal realization `S`
over `L` with unitary central character `χ`, the pullback `S.arithmeticComap e` has the
unitary central character `HeckeCharacter.comap e χ`, the composite of `χ` with the
idele class isomorphism induced by `e`. This proves
`ArithmeticComapUnitaryCentralCharacterStatement` at independent field universes.
-/

noncomputable section

universe uK uL

set_option autoImplicit false

namespace Langlands.Automorphic

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality

namespace CuspidalOperatorRealization

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)] {r : ℕ}

/-- The transported character: if `χ` is a unitary central character of `S`, then
`HeckeCharacter.comap e χ` is a unitary central character of `S.arithmeticComap e`. -/
theorem arithmeticComap_unitaryCentralCharacter (e : K ≃+* L)
    (S : CuspidalOperatorRealization L r) (χ : HeckeCharacter L)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ) :
    (∀ x, ‖(HeckeCharacter.comap e χ x : ℂ)‖ = 1) ∧
      (S.arithmeticComap e).HasCentralCharacter (HeckeCharacter.comap e χ) :=
  ⟨fun x => hχ (ideleClassEquiv e x), (S.arithmeticComap_hasCentralCharacter_iff e χ).mpr hS⟩

end CuspidalOperatorRealization

/-- Arithmetic pullback along a ring isomorphism of number fields preserves a unitary
central character, with witness the pulled-back Hecke character. -/
theorem arithmeticComapUnitaryCentralCharacter :
    ArithmeticComapUnitaryCentralCharacterStatement.{uK, uL} := by
  intro K L _ _ _ _ _ _ e r S hS
  obtain ⟨χ, hχ, hSχ⟩ := hS
  exact ⟨HeckeCharacter.comap e χ,
    S.arithmeticComap_unitaryCentralCharacter e χ hχ hSχ⟩

end Langlands.Automorphic
