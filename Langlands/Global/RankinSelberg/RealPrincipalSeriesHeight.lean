import Langlands.Global.RankinSelberg.RealMatrixHeightBounds
import Langlands.Global.RankinSelberg.RealLocalWhittakerProperties
import Langlands.Representation.Archimedean.RealJacquetMatrixCoefficient

/-! # A bound for the real position principal series by the compact supremum -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.RealJacquetCoefficient
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open RealPlaceRestriction

namespace RealPrincipalSeries

variable {n : ℕ}

private theorem trace_mul_transpose_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ (A * A.transpose).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

private theorem height_eq_traces (g : Langlands.GeneralLinear n ℝ) :
    realMatrixHeight g = (g.val * g.val.transpose).trace +
      ((g⁻¹).val * (g⁻¹).val.transpose).trace := by
  simp only [realMatrixHeight, Real.norm_eq_abs, sq_abs, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_add_distrib, ← pow_two]

/-- Multiplication on the left by an orthogonal matrix preserves the matrix height. -/
theorem realMatrixHeight_unitary_mul {k : Langlands.GeneralLinear n ℝ}
    (hk : k ∈ unitaryCompact ℝ n) (g : Langlands.GeneralLinear n ℝ) :
    realMatrixHeight (k * g) = realMatrixHeight g := by
  rw [height_eq_traces, height_eq_traces]
  simp only [Units.val_mul, mul_inv_rev]
  rw [trace_orth_mul _ _ (mul_eq_one_comm.mp (GramFormula.mul_transpose_eq_one_of_mem hk)),
    trace_mul_orth _ _
      (GramFormula.mul_transpose_eq_one_of_mem ((unitaryCompact ℝ n).inv_mem hk))]

private theorem abs_le_height_of_sq_le (hn : 0 < n) (g : Langlands.GeneralLinear n ℝ)
    (x : ℝ) (hx : x ^ 2 ≤ realMatrixHeight g) : |x| ≤ realMatrixHeight g := by
  have hH := two_le_realMatrixHeight hn g
  have hsq : |x| ^ 2 ≤ realMatrixHeight g := by rwa [sq_abs]
  nlinarith [sq_nonneg (|x| - 1)]

private theorem diagonal_height_bounds (hn : 0 < n) {g k : Langlands.GeneralLinear n ℝ}
    (d : Fin n → ℝˣ) (u : upperUnipotent n ℝ) (hk : k ∈ unitaryCompact ℝ n)
    (hg : g = (Iwasawa.diagonalUnits d : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * k) (i : Fin n) :
    |(d i : ℝ)| ≤ realMatrixHeight g ∧ |(d i : ℝ)|⁻¹ ≤ realMatrixHeight g := by
  have hd := sq_le_trace_of_iwasawa d u hk i
  rw [← hg] at hd
  refine ⟨abs_le_height_of_sq_le hn g _ (hd.trans ?_), ?_⟩
  · rw [height_eq_traces]
    exact le_add_of_nonneg_right (trace_mul_transpose_nonneg _)
  · let A : Matrix (Fin n) (Fin n) ℝ :=
      ((u⁻¹ : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ).val *
        Matrix.diagonal fun j => (d j : ℝ)⁻¹
    have hInv : g⁻¹ = k⁻¹ * ((u⁻¹ : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) *
        (Iwasawa.diagonalUnits (d⁻¹) : Langlands.GeneralLinear n ℝ) := by
      simp only [hg, mul_inv_rev, Subgroup.coe_inv, map_inv, mul_assoc]
    have hVal : (g⁻¹).val = (k⁻¹).val * A := by
      rw [hInv, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Iwasawa.diagonalUnits_val]
      simp only [A, Pi.inv_apply, Units.val_inv_eq_inv_val]
    have hDiag : A i i = (d i : ℝ)⁻¹ := by
      dsimp only [A]
      rw [Matrix.mul_diagonal, (u⁻¹).2.2 i, one_mul]
    have hOrtho : (k⁻¹).val.transpose * (k⁻¹).val = 1 :=
      mul_eq_one_comm.mp (GramFormula.mul_transpose_eq_one_of_mem ((unitaryCompact ℝ n).inv_mem hk))
    have hSquare : ((d i : ℝ)⁻¹) ^ 2 ≤ realMatrixHeight g := by
      calc
        _ = (A i i) ^ 2 := by rw [hDiag]
        _ ≤ (A * A.transpose).trace := sq_le_trace_mul_transpose A i
        _ = ((g⁻¹).val * (g⁻¹).val.transpose).trace := by
          rw [hVal, trace_orth_mul _ _ hOrtho]
        _ ≤ _ := by
          rw [height_eq_traces]
          exact le_add_of_nonneg_left (trace_mul_transpose_nonneg _)
    rw [← abs_inv]
    exact abs_le_height_of_sq_le hn g _ hSquare

/-- The compact supremum of a position principal-series vector controls its growth,
with a polynomial height exponent depending only on the inducing data. -/
def RealPrincipalSeriesHeightStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ ds : List RealBlock,
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
      ∀ (f : Langlands.GeneralLinear n ℝ → ℂ),
        f ∈ principalSeries ℝ n (realPositionCharacter ds) →
      ∀ (B : ℝ), (∀ k ∈ unitaryCompact ℝ n, ‖f k‖ ≤ B) →
        ∀ g, ‖f g‖ ≤ A * B * realMatrixHeight g ^ N

theorem realPrincipalSeriesHeight : RealPrincipalSeriesHeightStatement := by
  intro n hn ds
  let e (i : Fin n) := |(GramFormula.shiftedExponent n (GramFormula.realPositionExponent ds) i).re|
  let S := ∑ i, e i
  let A := ∏ i : Fin n, (‖realPositionCharacter ds i 1‖ + ‖realPositionCharacter ds i (-1)‖)
  let N := ⌈S⌉₊
  have hA : 0 ≤ A := Finset.prod_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨A, N, hA, fun f hf B hK g => ?_⟩
  obtain ⟨d, u, k, hk, hg⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  have hH : 1 ≤ realMatrixHeight g := le_trans (by norm_num) (two_le_realMatrixHeight hn g)
  have hlog (i : Fin n) : |Real.log (|(d i : ℝ)|)| ≤ Real.log (realMatrixHeight g) := by
    obtain ⟨hi, hi'⟩ := diagonal_height_bounds hn d u hk hg i
    exact Langlands.Global.abs_log_le_log_of_le (abs_pos.mpr (d i).ne_zero) hi hi'
  have hExp :
      Real.exp (∑ i, e i * |Real.log (|(d i : ℝ)|)|) ≤ realMatrixHeight g ^ N := by
    calc
      _ ≤ Real.exp (∑ i, e i * Real.log (realMatrixHeight g)) := by
        apply Real.exp_le_exp.mpr
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlog i) (abs_nonneg _)
      _ = realMatrixHeight g ^ S := by
        rw [← Finset.sum_mul, Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hH), mul_comm]
      _ ≤ realMatrixHeight g ^ (N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hH (Nat.le_ceil S)
      _ = _ := Real.rpow_natCast _ _
  have hChar : ‖principalSeriesCharacter ℝ n (realPositionCharacter ds) d‖ ≤
      A * realMatrixHeight g ^ N :=
    (norm_principalSeriesCharacter_le ds d).trans (mul_le_mul_of_nonneg_left hExp hA)
  have hf' : f g = principalSeriesCharacter ℝ n (realPositionCharacter ds) d * f k := by
    rw [hg]
    exact hf.2 d u k
  rw [hf', norm_mul]
  calc
    _ ≤ (A * realMatrixHeight g ^ N) * B :=
      mul_le_mul hChar (hK k hk) (norm_nonneg _) (mul_nonneg hA (pow_nonneg (le_trans zero_le_one hH) _))
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- One polynomial exponent works for all principal-series vectors and all their
right derivative words. The constant may depend on the vector and the word. -/
theorem exists_uniform_principalSeries_derivative_height (r : ℕ) (ds : List RealBlock) :
    ∃ N : ℕ, ∀ f : Langlands.GeneralLinear (r + 1) ℝ → ℂ,
      f ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds) →
      ∀ Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
          ‖RealLocalWhittaker.iteratedRightDerivative r Xs f g‖ ≤ C * realMatrixHeight g ^ N := by
  obtain ⟨A, N, hA, hBound⟩ := realPrincipalSeriesHeight (r + 1) (Nat.succ_pos r) ds
  refine ⟨N, fun f hf Xs => ?_⟩
  have hmem : RealLocalWhittaker.iteratedRightDerivative r Xs f ∈
      principalSeries ℝ (r + 1) (realPositionCharacter ds) := by
    induction Xs with
    | nil => exact hf
    | cons X Xs ih => exact rightDerivative_mem_principalSeries _ ih X
  let V := RealLocalWhittaker.iteratedRightDerivative r Xs f
  have hcont : Continuous fun k : unitaryCompact ℝ (r + 1) => V k :=
    hmem.1.continuous.comp continuous_subtype_val
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  have hB₀ := (norm_nonneg (V 1)).trans (hB 1 (Set.mem_univ _))
  exact ⟨A * B, mul_nonneg hA hB₀, hBound V hmem B (fun k hk =>
    hB ⟨k, hk⟩ (Set.mem_univ _))⟩

end RealPrincipalSeries

end Langlands.Global.RankinSelbergGlobal
