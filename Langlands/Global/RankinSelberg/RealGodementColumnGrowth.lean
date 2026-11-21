import Langlands.Global.RankinSelberg.RealGodementSmoothLeading
import Langlands.Global.RankinSelberg.RealGodementTranslatedSeminorm
import Langlands.Global.RankinSelberg.RealEqualDualConvergence

/-! # Common polynomial growth of real Godement column values -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealJacquetFrobenius RealPlaceRestriction

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

private theorem norm_determinantWeight_charData {n : ℕ} (p : Fin 2) (w s : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    ‖determinantWeight (charData p w) s g‖ = |g.val.det| ^ (w + s).re := by
  let d := determinant g
  have hPos : 0 < |(d : ℝ)| := abs_pos.mpr d.ne_zero
  change ‖((charData p w).character d : ℂ) * ((|(d : ℝ)| : ℝ) : ℂ) ^ s‖ = |(d : ℝ)| ^ (w + s).re
  rw [(charData p w).character_eq]
  simp only [charData, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs,
    div_self hPos.ne', one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hPos]
  rw [← Real.rpow_add hPos, Complex.add_re]

/-- A single upper group growth exponent works for every test and every lower coefficient
whose regular right derivatives share the given lower group growth exponent. -/
def RealGodementColumnGrowthStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (w : ℂ) (N : ℕ),
    ∃ M : ℕ, ∀ (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
      (∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
        RealLocalWhittaker.regularFunctions t (-a)) →
      (∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
        ‖RealLocalWhittaker.iteratedRightDerivative t Xs W g‖ ≤ C * realMatrixHeight g ^ N) →
      ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
        ‖godementLeadingFamily D a Φ W p g w‖ ≤ C * realMatrixHeight g ^ M

theorem realGodementColumnGrowth : RealGodementColumnGrowthStatement := by
  intro t D a p w N
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let s := w + (t : ℂ) / 2
  let S := (((t : ℂ) + 1) / 2)
  let R := |s.re - (t + 1 : ℕ)|
  obtain ⟨q, hq, hBounds⟩ := exists_columnMellin_uniform_seminorm μ a N R (abs_nonneg _)
  have hRank : 0 < t + 2 := by omega
  obtain ⟨I, L, A, hA, hQ⟩ := realGodementTranslatedSeminorm (t + 1) (t + 2) hRank q hq
  obtain ⟨C, K, hC, hD⟩ := exists_det_rpow_le_realMatrixHeight hRank (w + S).re
  refine ⟨K + L, fun W hReg hGrowth Φ => ?_⟩
  obtain ⟨B, hB, hB₀, hPoint⟩ := hBounds W hReg hGrowth
  let b := ∫ h, B h ∂μ
  let P := I.sup (schwartzSeminormFamily ℝ (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ) ℂ) Φ
  have hb : 0 ≤ b := integral_nonneg hB₀
  have hP : 0 ≤ P := apply_nonneg _ _
  refine ⟨C * (A * P * b), by positivity, fun g => ?_⟩
  let e := weylLong (t + 2) ℝ * g
  let Ψ := rectangularTranslate 1 e Φ
  let F := columnMellinIntegrand a Ψ W p.val s
  have hFi : Integrable F μ := (realGodementColumnConvergence t μ a Ψ W hReg ⟨N, hGrowth⟩ p.val).1 s
  have hF : ‖∫ h, F h ∂μ‖ ≤ q Ψ * b := by
    calc
      _ ≤ ∫ h, ‖F h‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ h, q Ψ * B h ∂μ := integral_mono hFi.norm (hB.const_mul _) (hPoint Ψ p.val s le_rfl)
      _ = _ := integral_const_mul _ _
  have hHeight : realMatrixHeight e = realMatrixHeight g :=
    RealPrincipalSeries.realMatrixHeight_unitary_mul (RealEqualDualConvergence.weylLong_mem_unitary (r := t + 1)) g
  have hDet : ‖determinantWeight (charData p w) S e‖ ≤ C * realMatrixHeight g ^ K := by
    rw [norm_determinantWeight_charData, ← hHeight]
    exact hD e
  have hTest : q Ψ ≤ A * realMatrixHeight g ^ L * P := by
    rw [← hHeight]
    exact hQ e Φ
  have hH : 0 ≤ realMatrixHeight g := realMatrixHeight_nonneg g
  change ‖determinantWeight (charData p w) S e * (∫ h, F h ∂μ)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (C * realMatrixHeight g ^ K) * (q Ψ * b) :=
      mul_le_mul hDet hF (norm_nonneg _) (by positivity)
    _ ≤ (C * realMatrixHeight g ^ K) * ((A * realMatrixHeight g ^ L * P) * b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hTest hb) (by positivity)
    _ = _ := by rw [pow_add]; ring

end Langlands.Global.RankinSelbergGlobal.RealGodement
