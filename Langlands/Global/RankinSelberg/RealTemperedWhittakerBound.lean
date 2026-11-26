import Langlands.Global.RankinSelberg.RankOneOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RealTemperedOrdinaryConvergence
import Langlands.Representation.Archimedean.RealGenericParameterReduction

/-! # The tempered Whittaker bound on the exact real coefficient model -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker

open ArchimedeanLocal RealIwasawa
open RealLocalWhittaker (iteratedRightDerivative_mem_model)

/-- The half-modulus estimate with arbitrarily small exponential loss in the logarithmic
Iwasawa diagonal, for each coefficient of a real block list with imaginary exponents. -/
def RealTemperedWhittakerBoundAtRank (r : ℕ) : Prop :=
  ∀ (ds : List RealBlock), realRank ds = r + 1 → (∀ d ∈ ds, realBlockExponent d = 0) →
    ∀ (a : ℝˣ) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      W ∈ realWhittakerModel r ds a → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
          ‖W (torus y * k.val)‖ ≤
            C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ j, |y j|)

/-- The scalar bound at a rank also bounds every right derivative of every coefficient. -/
theorem hasTemperedDerivativeBound_of_model {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (h : RealTemperedWhittakerBoundAtRank r) (hr : realRank ds = r + 1)
    (him : ∀ d ∈ ds, realBlockExponent d = 0) (hW : W ∈ realWhittakerModel r ds a) :
    HasTemperedDerivativeBound W := by
  intro ε hε Xs
  exact h ds hr him a _ (iteratedRightDerivative_mem_model hW Xs) ε hε

/-- The scalar bound at rank one follows from unitarity of the twisting character. -/
theorem realTemperedWhittakerBoundAtRank_zero : RealTemperedWhittakerBoundAtRank 0 := by
  intro ds hr him a W hW ε hε
  obtain ⟨c, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hr
  have hc : c.exponent.re = 0 := him (.character c) List.mem_cons_self
  obtain ⟨C, hC⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel hW
  have hnorm (g : Langlands.GeneralLinear 1 ℝ) : ‖W g‖ = ‖C‖ := by
    let d := (Langlands.GeneralLinear.determinant g : ℝ)
    have hd : 0 < |d| := abs_pos.mpr (Langlands.GeneralLinear.determinant g).ne_zero
    have hsign : |d / (|d|)| = 1 := by rw [abs_div, abs_abs, div_self hd.ne']
    rw [hC g, norm_mul, c.character_eq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    change ‖C‖ * (|d / (|d|)| ^ c.parity.val * ‖((|d| : ℝ) : ℂ) ^ c.exponent‖) = _
    rw [hsign, one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd, hc, Real.rpow_zero, mul_one]
  refine ⟨‖C‖, norm_nonneg _, fun y k => ?_⟩
  have hδ : torusModularLog 1 y = 0 := by simp [torusModularLog]
  rw [hnorm, hδ, zero_div, zero_add]
  exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by positivity))

end Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker
