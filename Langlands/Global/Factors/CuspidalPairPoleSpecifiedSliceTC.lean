import Langlands.Global.Factors.CuspidalPairPoleLocalRanges
import Langlands.Global.RankinSelberg.InfiniteWhittakerComplexSliceData

/-! # The specified Whittaker slice ranges for both characters over totally complex fields -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

namespace Langlands.Global.CuspidalPairPoles

open RankinSelbergGlobal HeckeFunctionalEquation

/-- The slice comparison for the ordinary local tests holds over every totally complex field. -/
def SpecifiedWhittakerSliceComparisonTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)], SpecifiedWhittakerSliceComparisonAt.{u,uQ} F

theorem specifiedWhittakerSliceComparisonTC : SpecifiedWhittakerSliceComparisonTCStatement.{u,uQ} := by
  intro F _ _ _ _ ψ hψ r T _ P hP aR _ aC haC dR _ dC hdC
  let ψ' := inverseCharacter ψ
  have haC' (w : {w : InfinitePlace F // w.IsComplex}) :
      IsComplexAdditiveComponent ψ' w.1 w.2 (-aC w) := by
    intro y
    apply Subtype.ext
    change ψ'.complex (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) = _
    rw [show ψ'.complex = ψ.complex⁻¹ from complex_inverseCharacter ψ]
    exact complexComponent_complex_inv ψ w (aC w) (haC w) y
  obtain ⟨M, hM⟩ := infiniteWhittakerComplexSliceData F ψ hψ r T P hP aC haC dC hdC
  obtain ⟨N, hN⟩ := infiniteWhittakerComplexSliceData F ψ' (inverseCharacter_rational ψ hψ)
    r T P hP (fun w => -aC w) haC' dC hdC
  let : IsEmpty {v : InfinitePlace F // v.IsReal} :=
    ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex v.1) v.2⟩
  exact ⟨M, N, ⟨isEmptyElim, hM⟩, ⟨isEmptyElim, hN⟩⟩

end Langlands.Global.CuspidalPairPoles
