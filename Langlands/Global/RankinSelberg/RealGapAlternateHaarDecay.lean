import Langlands.Global.RankinSelberg.RealGapAlternateRetained
import Langlands.Global.RankinSelberg.RealGapTorusBound

/-! # Exponential decay for the real weighted logarithmic tail Haar -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapAlternateHaarDecay

open Langlands.GeneralLinear (UpperEntryPair blockSum)
open ArchimedeanLocal (realNormalizedAbs)
open RealGapRightChart (consecutiveTailWeight measurable_consecutiveTailWeight)
open RealGapTailIwasawa (tailModulus measurable_tailModulus tailDiagonalMeasure)
open RealGapTriangularChart (Outer retainedMatrix diagonalWeightMeasure)
open RealGapUpperTail (packedTail firstRectangle)
open RealIwasawa (torus torus_val continuous_torus)
open RealConvergenceAnalysis (lintegral_exp_neg_mul_sum_abs_lt_top)

local notation "Y" => fun q => Fin (q + 1) → ℝ
local notation "S" => fun {q : ℕ} (y : Y q) => ∑ i, |y i|
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))

local instance gapDiagonalDecayGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
local instance gapDiagonalDecayGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩

/-- The logarithmic tail diagonal has an exponential absolute determinant. -/
theorem normalizedDet_torus {n : ℕ} (y : Fin n → ℝ) :
    δ (torus y) = Real.exp (∑ i, y i) := by
  unfold realNormalizedAbs
  dsimp only
  rw [torus_val, Matrix.det_diagonal, ← Real.exp_sum, abs_of_pos (Real.exp_pos _)]

/-- The retained matrix has the same absolute determinant as its tail diagonal. -/
theorem normalizedDet_retained {k q : ℕ} (p : Outer k q) :
    δ (retainedMatrix k q p) = Real.exp (∑ i, p.1.1.2 i) := by
  let D : Langlands.GeneralLinear (k + (q + 1)) ℝ :=
    blockSum (n := k) (m := q + 1) ((1 : Langlands.GeneralLinear k ℝ), torus p.1.1.2)
  let U := packedTail k q (firstRectangle k q p.2) 1
  have hκ : |p.1.2.val.val.det| = 1 :=
    Langlands.Archimedean.RealJacquetCoefficient.abs_det_eq_one_of_mem p.1.2.2
  have hD : D.val.det = (torus p.1.1.2).val.det := by
    change (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (torus p.1.1.2).val)).det = _
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have hU : U.val.val.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular U.2.1, Finset.prod_eq_one fun i _ => U.2.2 i]
  change δ (p.1.2.val * D * U.val) = _
  unfold realNormalizedAbs
  dsimp only
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hU, mul_one, hD,
    abs_mul, hκ, one_mul]
  exact normalizedDet_torus _

/-- A coefficient bounding both diagonal densities in terms of the sum of absolute logs. -/
def diagonalGrowth (k q : ℕ) : ℝ := k + 2 * Fintype.card (UpperEntryPair (q + 1))

theorem diagonalGrowth_nonneg (k q : ℕ) : 0 ≤ diagonalGrowth k q := by
  unfold diagonalGrowth
  positivity

private theorem tailModulus_le (q : ℕ) (y : Y q) :
    (tailModulus y : ℝ) ≤ Real.exp ((2 * Fintype.card (UpperEntryPair (q + 1)) : ℝ) * S y) := by
  unfold tailModulus
  rw [NNReal.coe_prod]
  have hb (i : Fin (q + 1)) : |y i| ≤ S y :=
    Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ i)
  calc
    _ ≤ ∏ _ij : UpperEntryPair (q + 1), Real.exp (2 * S y) := by
      refine Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) (fun ij _ => ?_)
      change (((‖Real.exp (y ij.val.2 - y ij.val.1)‖₊)⁻¹ : ℝ≥0) : ℝ) ≤ _
      rw [NNReal.coe_inv, coe_nnnorm, Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      linarith only [(le_abs_self (y ij.val.1)).trans (hb ij.val.1),
        (neg_le_abs (y ij.val.2)).trans (hb ij.val.2)]
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      congr 1
      ring

private theorem consecutiveTailWeight_le (k q : ℕ) (y : Y q) :
    (consecutiveTailWeight k q (torus y) : ℝ) ≤ Real.exp ((k : ℝ) * S y) := by
  change (((‖(torus y).val.det‖₊ ^ k)⁻¹ : ℝ≥0) : ℝ) ≤ _
  rw [NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs]
  change ((δ (torus y)) ^ k)⁻¹ ≤ _
  rw [normalizedDet_torus, ← Real.exp_nat_mul, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h : -(∑ i, y i) ≤ S y := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => neg_le_abs _
  nlinarith only [mul_le_mul_of_nonneg_left h (show 0 ≤ (k : ℝ) by positivity)]

private theorem diagonalDensity_le (k q : ℕ) (y : Y q) :
    (tailModulus y : ℝ) * (consecutiveTailWeight k q (torus y) : ℝ) ≤
      Real.exp (diagonalGrowth k q * S y) := by
  refine (mul_le_mul (tailModulus_le q y) (consecutiveTailWeight_le k q y)
    (NNReal.coe_nonneg _) (Real.exp_nonneg _)).trans_eq ?_
  rw [← Real.exp_add]
  unfold diagonalGrowth
  congr 1
  ring

/-- Exponential decay after paying for the exact diagonal Haar density. -/
def diagonalDecay (k q : ℕ) (y : Y q) : ℝ :=
  Real.exp (-(diagonalGrowth k q + 1) * S y)

/-- The diagonal exponential is integrable on the exact measure of the triangular chart. -/
def RealGapAlternateHaarDecayStatement : Prop :=
  ∀ k q : ℕ, Integrable (diagonalDecay k q) (diagonalWeightMeasure k q)

set_option maxHeartbeats 700000 in
theorem realGapAlternateHaarDecay : RealGapAlternateHaarDecayStatement := by
  intro k q
  let ρ := fun y : Y q => (tailModulus y : ℝ≥0∞)
  let θ := fun y : Y q => (consecutiveTailWeight k q (torus y) : ℝ≥0∞)
  let f := fun y : Y q => ENNReal.ofReal (diagonalDecay k q y)
  have hρ : Measurable ρ := measurable_tailModulus
  have hθ : Measurable θ := (measurable_consecutiveTailWeight k q).comp continuous_torus.measurable
  have hS : Continuous (fun y : Y q => S y) := continuous_finsetSum _ fun i _ => (continuous_apply i).abs
  have hf : Continuous (diagonalDecay k q) := Real.continuous_exp.comp (continuous_const.mul hS)
  have hf' : Measurable f := ENNReal.measurable_ofReal.comp hf.measurable
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp_rw [show ∀ y : Y q, ‖diagonalDecay k q y‖ = diagonalDecay k q y from
    fun y => Real.norm_of_nonneg (Real.exp_nonneg _)]
  change (∫⁻ y, f y ∂(volume.withDensity ρ).withDensity θ) < ⊤
  rw [← withDensity_mul volume hρ hθ, lintegral_withDensity_eq_lintegral_mul _ (hρ.mul hθ) hf']
  calc
    _ ≤ ∫⁻ y : Y q, ENNReal.ofReal (Real.exp (-1 * S y)) := by
      refine lintegral_mono fun y => ?_
      change ρ y * θ y * f y ≤ _
      rw [show ρ y = ENNReal.ofReal (tailModulus y : ℝ) from ENNReal.ofReal_coe_nnreal.symm,
        show θ y = ENNReal.ofReal (consecutiveTailWeight k q (torus y) : ℝ) from ENNReal.ofReal_coe_nnreal.symm,
        show f y = ENNReal.ofReal (diagonalDecay k q y) from rfl,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), ← ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      refine (mul_le_mul_of_nonneg_right (diagonalDensity_le k q y) (Real.exp_nonneg _)).trans_eq ?_
      rw [← Real.exp_add]
      congr 1
      ring
    _ < ⊤ := lintegral_exp_neg_mul_sum_abs_lt_top one_pos

end Langlands.Global.RankinSelbergGlobal.RealGapAlternateHaarDecay
