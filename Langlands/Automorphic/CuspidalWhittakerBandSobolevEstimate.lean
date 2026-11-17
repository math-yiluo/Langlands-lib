import Langlands.Automorphic.CuspidalWhittakerBandBound
import Langlands.Automorphic.OperatorCompactSobolevStatement

/-! # Conditional Sobolev estimates for actual Whittaker coefficients -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.MonObj NumberField

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.RankinSelbergGlobal
  ContinuousRationalFunctions MeasureTheory

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)

set_option maxHeartbeats 1600000 in
/-- The compact Sobolev premise implies the actual Whittaker band bound.
The compact domination set is independent of the vector and the bound. -/
theorem cuspWhittakerBandBound_of_compactSobolev
    (hSobolev : OperatorCompactSobolevStatement.{u})
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (hL2 : ∀ x : T.Space,
      MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization x) 2
        ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
          (OperatorDeterminantSlice.band F (r + 1))))
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) :
    CuspidalWhittakerBandBound F T hL2 ψ := by
  intro J hJo hJc Q hQ
  obtain ⟨K, hK, hdom⟩ := Unfolding.exists_isCompact_cuspWhittaker_domination F Q hQ
  obtain ⟨D, C, hC, hbound⟩ :=
    hSobolev F r T.realization χ hχ hTχ hL2 J hJo hJc K hK
  refine ⟨D, C, hC, ?_⟩
  intro v hv g hg
  exact hdom T ψ hψ v _ (hbound v hv) g hg


end Langlands.Automorphic
