import Langlands.Global.Factors.CuspidalPairPoleLocalRanges
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerRange

/-! # The converse complex Whittaker restriction for both characters -/

noncomputable section

universe u

open NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.CuspidalPairPoles

open HeckeFunctionalEquation RankinSelbergGlobal

theorem complexPlaceWhittakerRestrictionSurjectivity :
    ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u} := by
  intro F _ _ _ ψ hψ r T _ w a ha d hd W
  constructor
  · intro hW
    obtain ⟨x, hx⟩ := complexPlaceWhittakerRange F ψ hψ r T w d hd a ha W hW
    exact ⟨x, 1, funext fun g => by rw [InfiniteWhittakerSlice.finitePoint_one, mul_one, hx g]⟩
  · intro hW
    let ψ' := inverseCharacter ψ
    have ha' : IsComplexAdditiveComponent ψ' w.1 w.2 (-a) := by
      intro y
      apply Subtype.ext
      change ψ'.complex (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) = _
      rw [show ψ'.complex = ψ.complex⁻¹ from complex_inverseCharacter ψ]
      exact complexComponent_complex_inv ψ w a ha y
    obtain ⟨x, hx⟩ := complexPlaceWhittakerRange F ψ' (inverseCharacter_rational ψ hψ) r T w d hd
      (-a) ha' W hW
    refine ⟨x, 1, funext fun g => ?_⟩
    rw [InfiniteWhittakerSlice.finitePoint_one, mul_one]
    simpa only [ψ', complex_inverseCharacter] using hx g

end Langlands.Global.CuspidalPairPoles
