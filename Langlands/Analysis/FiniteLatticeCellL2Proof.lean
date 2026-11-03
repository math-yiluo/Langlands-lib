import Langlands.Analysis.FiniteLatticeCellL2Statement
import Langlands.Analysis.CountableCellLpProof
import Langlands.Analysis.FiniteNatLatticeSummabilityProof

/-! # L2 integration from polynomial-geometric finite lattice cell bounds -/

namespace Langlands

open MeasureTheory
open scoped BigOperators ENNReal

theorem finiteLatticeCellL2.{uX, uI} :
    FiniteLatticeCellL2Statement.{uX, uI} := by
  intro X _ I _ μ f hf cell hcover C D hC hD a w ha hw hres d hcoef hvol
  classical
  let height : (I → ℕ) → ℝ := fun n => 1 + ∑ i, (n i : ℝ)
  let bound : (I → ℕ) → ℝ := fun n =>
    C * height n ^ d * ∏ i, (a i) ^ n i
  let residual : I → ℝ := fun i => (a i) ^ 2 * w i
  have hheight (n : I → ℕ) : 0 ≤ height n := by
    dsimp [height]
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)
  have hbound (n : I → ℕ) : 0 ≤ bound n :=
    mul_nonneg (mul_nonneg hC (pow_nonneg (hheight n) _))
      (Finset.prod_nonneg fun i _ => pow_nonneg (ha i) _)
  have halgebra (n : I → ℕ) :
      (bound n) ^ 2 * (D * ∏ i, (w i) ^ n i) =
        (C ^ 2 * D) * (height n ^ (2 * d) * ∏ i, (residual i) ^ n i) := by
    have hprod :
        (∏ i, (a i) ^ n i) ^ 2 * ∏ i, (w i) ^ n i =
          ∏ i, (residual i) ^ n i := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      dsimp [residual]
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (n i) 2]
    dsimp [bound]
    rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm d 2]
    calc
      _ = (C ^ 2 * D) * (height n ^ (2 * d) *
          ((∏ i, (a i) ^ n i) ^ 2 * ∏ i, (w i) ^ n i)) := by ring
      _ = _ := by rw [hprod]
  have hlattice :
      (∑' n : I → ℕ, ENNReal.ofReal
        (height n ^ (2 * d) * ∏ i, (residual i) ^ n i)) < ∞ := by
    simpa only [height, Real.rpow_eq_pow, Real.rpow_natCast] using
      finiteNatLatticeENNRealSummability I residual
        (fun i => mul_nonneg (sq_nonneg _) (hw i)) hres
        (2 * d : ℕ) (by positivity)
  let b : (I → ℕ) → ℝ≥0∞ := fun n => ENNReal.ofReal (bound n)
  have hb (n : I → ℕ) (x : X) (hx : x ∈ cell n) : ‖f x‖ₑ ≤ b n := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hcoef n x hx)
  have hterm (n : I → ℕ) :
      (b n) ^ (2 : ℝ≥0∞).toReal * μ (cell n) ≤
        ENNReal.ofReal (C ^ 2 * D) *
          ENNReal.ofReal (height n ^ (2 * d) * ∏ i, (residual i) ^ n i) := by
    calc
      _ ≤ (b n) ^ (2 : ℝ≥0∞).toReal *
          ENNReal.ofReal (D * ∏ i, (w i) ^ n i) := by
        gcongr
        exact hvol n
      _ = ENNReal.ofReal
          ((bound n) ^ 2 * (D * ∏ i, (w i) ^ n i)) := by
        simp only [b, ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg
          (hbound n) (by positivity : (0 : ℝ) ≤ 2), Real.rpow_two]
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      _ = _ := by
        rw [halgebra, ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hD)]
  have hsum :
      (∑' n, (b n) ^ (2 : ℝ≥0∞).toReal * μ (cell n)) < ∞ := by
    calc
      _ ≤ ∑' n : I → ℕ, ENNReal.ofReal (C ^ 2 * D) *
          ENNReal.ofReal (height n ^ (2 * d) * ∏ i, (residual i) ^ n i) :=
        ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (C ^ 2 * D) *
          ∑' n : I → ℕ, ENNReal.ofReal
            (height n ^ (2 * d) * ∏ i, (residual i) ^ n i) :=
        ENNReal.tsum_mul_left
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlattice
  exact countableCellLpUpper X (I → ℕ) μ f 2 (by norm_num) (by norm_num)
    hf cell hcover b hb hsum

end Langlands
