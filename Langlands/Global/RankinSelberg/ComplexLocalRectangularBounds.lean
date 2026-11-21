import Langlands.Global.RankinSelberg.ComplexLocalIwasawa
import Langlands.Global.RankinSelberg.RectangularIwasawaBounds
import Langlands.Global.RankinSelberg.RectangularIwasawaChart
import Langlands.Global.RankinSelberg.RealConvergenceAnalysis
import Langlands.Group.GL.ReindexCongr

/-! # Iwasawa bounds for the complex rectangular kernel -/

noncomputable section
open scoped Classical Matrix
open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalRectangularBounds

open ComplexLocalIwasawa
open ComplexLocalWhittakerGauge (logTorus logTorus_val logTorus_inv_val)
open RealConvergenceAnalysis (rootPos rootPos_nonneg sub_last_le)

/-- Logarithm of one plus the sum of the squared rectangular entry norms. -/
def logRectangleSize {m d : ℕ} (x : Matrix (Fin d) (Fin m) ℂ) : ℝ :=
  Real.log (1 + ∑ i, ∑ j, ‖x i j‖ ^ 2)

theorem logRectangleSize_nonneg {m d : ℕ} (x : Matrix (Fin d) (Fin m) ℂ) :
    0 ≤ logRectangleSize x := by
  apply Real.log_nonneg
  exact le_add_of_nonneg_right (by positivity)

theorem continuous_logRectangleSize {m d : ℕ} :
    Continuous (logRectangleSize (m := m) (d := d)) := by
  unfold logRectangleSize
  have h : Continuous (fun x : Matrix (Fin d) (Fin m) ℂ => 1 + ∑ i, ∑ j, ‖x i j‖ ^ 2) :=
    continuous_const.add (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => (continuous_apply_apply i j).norm.pow 2)
  exact h.log fun x => ne_of_gt (by positivity)

private theorem sqSize_eq_gramTrace {m d : ℕ} (x : Matrix (Fin d) (Fin m) ℂ) :
    (∑ i, ∑ j, ‖x i j‖ ^ 2) = ((x * xᴴ).trace).re := by
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Langlands.Archimedean.ComplexGramFormula.self_mul_conj_eq,
    Complex.ofReal_re]

theorem logRectangleSize_mul_unitary {m d : ℕ} (x : Matrix (Fin d) (Fin m) ℂ)
    (k : unitaryCompact ℂ m) : logRectangleSize (x * k.val.val) = logRectangleSize x := by
  unfold logRectangleSize
  rw [sqSize_eq_gramTrace, sqSize_eq_gramTrace]
  have hk := Matrix.mem_unitaryGroup_iff.mp k.2
  rw [Matrix.star_eq_conjTranspose] at hk
  have h : (x * k.val.val) * (x * k.val.val)ᴴ = x * xᴴ := by
    calc
      _ = x * (k.val.val * k.val.valᴴ) * xᴴ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hk, Matrix.mul_one]
  rw [h]

private theorem entry_le_exp_logRectangleSize {m d : ℕ} (x : Matrix (Fin d) (Fin m) ℂ)
    (i : Fin d) (j : Fin m) : ‖x i j‖ ≤ Real.exp (logRectangleSize x) := by
  rw [logRectangleSize, Real.exp_log (by positivity)]
  have h : ‖x i j‖ ^ 2 ≤ ∑ p, ∑ q, ‖x p q‖ ^ 2 :=
    (Finset.single_le_sum (fun q _ => sq_nonneg ‖x i q‖) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg ‖x p q‖)
        (Finset.mem_univ i))
  nlinarith [sq_nonneg (‖x i j‖ - 1)]

theorem logRectangleSize_extend {m d : ℕ} (x : Matrix (Fin d) (Fin m) ℂ) :
    logRectangleSize (RectangularIwasawa.extendRectangle 1 x) = logRectangleSize x := by
  unfold logRectangleSize
  rw [Fin.sum_univ_castSucc]
  simp [RectangularIwasawa.extendRectangle, Fin.append_right_eq_snoc]

/-! ### The diagonal and inverse diagonal of the triangular factor -/

private theorem bpart_eq {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    bpart g = (npart g).val * logTorus (alpha g) := by
  change g * (kpart g).val⁻¹ = _
  calc
    g * (kpart g).val⁻¹ =
        ((npart g).val * logTorus (alpha g) * (kpart g).val) * (kpart g).val⁻¹ := by
      rw [npart_mul_logTorus_mul_kpart]
    _ = _ := mul_inv_cancel_right _ _

private theorem bpart_upper {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    (bpart g).val.IsUpperTriangular := by
  rw [bpart_eq, Units.val_mul, logTorus_val]
  exact LinearAlgebra.TriangularUnitary.isUpperTriangular_mul_diagonal (npart g).2.1 _

theorem exp_neg_alpha {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (i : Fin n) :
    (Real.exp (-alpha g i) : ℂ) = (bpart g)⁻¹.val i i := by
  rw [bpart_eq, mul_inv_rev, Units.val_mul, logTorus_inv_val, Matrix.diagonal_mul]
  have h : ((npart g).val⁻¹).val i i = 1 :=
    GeneralLinear.UpperUnipotent.entry_diag (npart g)⁻¹ i
  rw [h, mul_one]

private theorem unitary_entry_le {n : ℕ} (k : unitaryCompact ℂ n) (i j : Fin n) :
    ‖k.val.val i j‖ ≤ 1 :=
  LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup k.2 i j

private theorem norm_matMul_entry_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    {a b : ℝ} (ha : 0 ≤ a) (hA : ∀ k, ‖A i k‖ ≤ a) (hB : ∀ k, ‖B k j‖ ≤ b) :
    ‖(A * B) i j‖ ≤ (n : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, a * b := Finset.sum_le_sum fun k _ => by
      rw [norm_mul]
      exact mul_le_mul (hA k) (hB k) (norm_nonneg _) ha
    _ = _ := by simp [nsmul_eq_mul]

private theorem alpha_le_of_row {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (i : Fin n)
    (T : ℝ) (hrow : ∀ j, ‖g.val i j‖ ≤ Real.exp T) :
    alpha g i ≤ Real.log (n : ℝ) + T := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  apply Real.exp_le_exp.mp
  rw [Real.exp_add, Real.exp_log hn]
  have h := norm_matMul_entry_le g.val ((kpart g)⁻¹).val.val i i (Real.exp_nonneg T)
    hrow (fun j => unitary_entry_le (kpart g)⁻¹ j i)
  change ‖(bpart g).val i i‖ ≤ _ at h
  rw [← exp_alpha, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), mul_one] at h
  exact h

private theorem neg_alpha_le_of_invCol {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (i : Fin n)
    (T : ℝ) (hcol : ∀ j, ‖g⁻¹.val j i‖ ≤ Real.exp T) :
    -alpha g i ≤ Real.log (n : ℝ) + T := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  apply Real.exp_le_exp.mp
  rw [Real.exp_add, Real.exp_log hn]
  have h := norm_matMul_entry_le (kpart g).val.val g⁻¹.val i i zero_le_one
    (fun j => unitary_entry_le (kpart g) i j) hcol
  rw [one_mul] at h
  have he : (bpart g)⁻¹ = (kpart g).val * g⁻¹ := by rw [bpart, mul_inv_rev, inv_inv]
  have h' : ‖(bpart g)⁻¹.val i i‖ ≤ (n : ℝ) * Real.exp T := by
    rw [he]
    exact h
  rw [← exp_neg_alpha, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at h'
  exact h'

private theorem alpha_last_eq_zero_of_standard_row {r : ℕ} (g : Langlands.GeneralLinear (r + 1) ℂ)
    (hrow : ∀ j, g.val (Fin.last r) j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.last r) j) :
    alpha g (Fin.last r) = 0 := by
  let i := Fin.last r
  have hle : ‖(bpart g).val i i‖ ≤ 1 := by
    change ‖(g.val * ((kpart g)⁻¹).val.val) i i‖ ≤ 1
    have hm : (g.val * ((kpart g)⁻¹).val.val) i i =
        ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) * ((kpart g)⁻¹).val.val) i i := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => congrArg
        (fun z => z * ((kpart g)⁻¹).val.val j i) (hrow j)
    rw [hm, Matrix.one_mul]
    exact unitary_entry_le (kpart g)⁻¹ i i
  have hge : 1 ≤ ‖(bpart g).val i i‖ := by
    have hg := congrArg (fun a : Langlands.GeneralLinear (r + 1) ℂ => a.val i i) (bpart_mul_kpart g)
    change ((bpart g).val * (kpart g).val.val) i i = g.val i i at hg
    rw [Matrix.mul_apply, Fintype.sum_eq_single i, hrow i, Matrix.one_apply_eq] at hg
    · have hn := congrArg norm hg
      rw [norm_mul, norm_one] at hn
      calc
        1 = ‖(bpart g).val i i‖ * ‖(kpart g).val.val i i‖ := hn.symm
        _ ≤ ‖(bpart g).val i i‖ * 1 :=
          mul_le_mul_of_nonneg_left (unitary_entry_le (kpart g) i i) (norm_nonneg _)
        _ = _ := mul_one _
    · intro j hj
      have hji : j < i := lt_of_le_of_ne (Fin.le_last j) hj
      have hz : (bpart g).val i j = 0 := bpart_upper g hji
      rw [hz, zero_mul]
  have he := le_antisymm hle hge
  rw [← exp_alpha, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_zero] at he
  exact Real.exp_injective he

/-! ### Entries of the rectangular point -/

section Block

variable {m d : ℕ}

local notation "G" => Langlands.GeneralLinear (m + d + 1) ℂ
local notation "Rect" => Matrix (Fin (d + 1)) (Fin m) ℂ

private def blockPoint (y : Fin m → ℝ) (x : Rect) : G :=
  lowerBlockPair (a := m) (d := d + 1) (logTorus y) x 1

private theorem blockPoint_inv (y : Fin m → ℝ) (x : Rect) :
    (blockPoint y x)⁻¹ =
      lowerBlockPair (a := m) (d := d + 1) (logTorus (-y)) (-x * (logTorus (-y)).val) 1 := by
  rw [blockPoint, lowerBlockPair_inv, ← logTorus_neg]
  simp

private theorem logTorus_entry_le {m : ℕ} (y : Fin m → ℝ) (i j : Fin m) {T : ℝ}
    (hy : y j ≤ T) :
    ‖(logTorus y).val i j‖ ≤ Real.exp T := by
  rw [logTorus_val]
  by_cases he : i = j
  · subst i
    rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_monotone hy
  · rw [Matrix.diagonal_apply_ne _ he, norm_zero]
    exact Real.exp_nonneg _

private theorem blockPoint_entry_le (y : Fin m → ℝ) (x : Rect) (i j : Fin (m + d + 1)) :
    ‖(blockPoint y x).val i j‖ ≤ Real.exp ((∑ j, |y j|) + logRectangleSize x) := by
  let S := ∑ j, |y j|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hX := logRectangleSize_nonneg x
  have h1 : 1 ≤ Real.exp (S + logRectangleSize x) :=
    Real.one_le_exp_iff.mpr (add_nonneg hS hX)
  refine Fin.addCases (m := m) (n := d + 1) (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (m := m) (n := d + 1) (fun j => ?_) (fun j => ?_) j
  · rw [blockPoint, lowerBlockPair_11]
    apply logTorus_entry_le
    have hsum : |y j| ≤ S :=
      Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ j)
    linarith [le_abs_self (y j)]
  · rw [blockPoint, lowerBlockPair_12, norm_zero]
    exact zero_le_one.trans h1
  · rw [blockPoint, lowerBlockPair_21]
    exact (entry_le_exp_logRectangleSize x i j).trans
      (Real.exp_monotone (le_add_of_nonneg_left hS))
  · rw [blockPoint, lowerBlockPair_22]
    exact (show ‖(1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j‖ ≤ 1 by
      rw [Matrix.one_apply]
      split_ifs <;> simp).trans h1

private theorem blockPoint_inv_leadingCol (y : Fin m → ℝ) (x : Rect)
    (i : Fin (m + d + 1)) (j : Fin m) :
    ‖(blockPoint y x)⁻¹.val i (j.castAdd (d + 1))‖ ≤ Real.exp (-y j + logRectangleSize x) := by
  rw [blockPoint_inv]
  refine Fin.addCases (m := m) (n := d + 1) (fun i => ?_) (fun i => ?_) i
  · rw [lowerBlockPair_11]
    apply logTorus_entry_le
    exact le_add_of_nonneg_right (logRectangleSize_nonneg x)
  · rw [lowerBlockPair_21, logTorus_val, Matrix.mul_diagonal, Matrix.neg_apply, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), Pi.neg_apply, Real.exp_add, mul_comm]
    exact mul_le_mul_of_nonneg_left (entry_le_exp_logRectangleSize x i j) (Real.exp_nonneg _)

private theorem blockPoint_inv_entry_le (y : Fin m → ℝ) (x : Rect) (i j : Fin (m + d + 1)) :
    ‖(blockPoint y x)⁻¹.val i j‖ ≤ Real.exp ((∑ j, |y j|) + logRectangleSize x) := by
  let S := ∑ j, |y j|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : 1 ≤ Real.exp (S + logRectangleSize x) :=
    Real.one_le_exp_iff.mpr (add_nonneg hS (logRectangleSize_nonneg x))
  refine Fin.addCases (m := m) (n := d + 1) (fun j => ?_) (fun j => ?_) j
  · have hsum : |y j| ≤ S :=
      Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ j)
    exact (blockPoint_inv_leadingCol y x i j).trans (Real.exp_monotone
      (add_le_add (le_trans (neg_le_abs _) hsum) le_rfl))
  · rw [blockPoint_inv]
    refine Fin.addCases (m := m) (n := d + 1) (fun i => ?_) (fun i => ?_) i
    · rw [lowerBlockPair_12, norm_zero]
      exact zero_le_one.trans h1
    · rw [lowerBlockPair_22]
      exact (show ‖(1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j‖ ≤ 1 by
        rw [Matrix.one_apply]
        split_ifs <;> simp).trans h1

private theorem blockPoint_last (y : Fin m → ℝ) (x : Rect)
    (hx : ∀ j, x (Fin.last d) j = 0) :
    alpha (blockPoint y x) (Fin.last (m + d)) = 0 := by
  apply alpha_last_eq_zero_of_standard_row
  have hi : Fin.last (m + d) = (Fin.last d).natAdd m := Fin.ext (by simp)
  intro j
  rw [hi]
  refine Fin.addCases (m := m) (n := d + 1) (fun j => ?_) (fun j => ?_) j
  · have hne : (Fin.last d).natAdd m ≠ j.castAdd (d + 1) := by
      intro h
      have hv := congrArg (fun a : Fin (m + d + 1) => a.val) h
      simp only [Fin.val_natAdd, Fin.val_last, Fin.val_castAdd] at hv
      omega
    rw [blockPoint, lowerBlockPair_21, hx, Matrix.one_apply_ne hne]
  · rw [blockPoint, lowerBlockPair_22]
    have he : (Fin.last d).natAdd m = j.natAdd m ↔ Fin.last d = j := by
      constructor
      · intro h
        apply Fin.ext
        have hv := congrArg (fun a : Fin (m + d + 1) => a.val) h
        simp only [Fin.val_natAdd] at hv
        omega
      · rintro rfl
        rfl
    change (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (Fin.last d) j = _
    simp only [Matrix.one_apply, he]

private theorem blockPoint_length_le (y : Fin m → ℝ) (x : Rect) :
    (∑ i, |alpha (blockPoint y x) i|) ≤ (((m + d + 1 : ℕ) : ℝ)) *
      (Real.log (((m + d + 1 : ℕ) : ℝ)) + (∑ j, |y j|) + logRectangleSize x) := by
  let T := (∑ j, |y j|) + logRectangleSize x
  let n := m + d + 1
  have h (i : Fin n) : |alpha (blockPoint y x) i| ≤ Real.log (n : ℝ) + T := by
    rw [abs_le]
    exact ⟨neg_le.mp (neg_alpha_le_of_invCol (blockPoint y x) i T
      (fun j => blockPoint_inv_entry_le y x j i)),
      alpha_le_of_row (blockPoint y x) i T (fun j => blockPoint_entry_le y x i j)⟩
  calc
    _ ≤ ∑ _i : Fin n, (Real.log (n : ℝ) + T) := Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

private theorem blockPoint_entry_le_roots (y : Fin m → ℝ) (x : Rect)
    (hx : ∀ j, x (Fin.last d) j = 0) (i : Fin (d + 1)) (j : Fin m) :
    ‖x i j‖ ≤ (((d + 1).factorial : ℕ) : ℝ) *
      Real.exp (((d + 1 : ℕ) : ℝ) * rootPos (alpha (blockPoint y x))) := by
  let g := blockPoint y x
  let z := alpha g
  have hz (i : Fin (m + d + 1)) : z i ≤ rootPos z := by
    have hlast : z (Fin.last (m + d)) = 0 := blockPoint_last y x hx
    simpa only [hlast, sub_zero] using sub_last_le z i
  have hprod : ‖RectangularIwasawa.trailingDiagonalProduct m (d + 1) (bpart g).val‖ =
      Real.exp (∑ i : Fin (d + 1), z (i.natAdd m)) := by
    rw [RectangularIwasawa.trailingDiagonalProduct, norm_prod, Real.exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← exp_alpha, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hcoord := RectangularIwasawa.norm_lowerBlockPair_coordinate_le_of_unitary
    (logTorus y) x (bpart g).val (kpart g).val.val (bpart_upper g) (kpart g).2
    (by change g.val = _; rw [← Units.val_mul, bpart_mul_kpart]) i j
  rw [hprod, mul_comm] at hcoord
  exact hcoord.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (by
    calc
      _ ≤ ∑ _l : Fin (d + 1), rootPos z := Finset.sum_le_sum fun l _ => hz (l.natAdd m)
      _ = _ := by
        change _ = (((d + 1 : ℕ) : ℝ)) * rootPos z
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]))
    (Nat.cast_nonneg _))

private def rectangleConstant (m d : ℕ) : ℝ :=
  1 + (((d + 1 : ℕ) : ℝ) * (m : ℝ)) * ((d + 1).factorial : ℝ) ^ 2

private theorem rectangleConstant_one_le (m d : ℕ) : 1 ≤ rectangleConstant m d := by
  unfold rectangleConstant
  exact le_add_of_nonneg_right (by positivity)

private theorem logRectangleSize_le_roots (y : Fin m → ℝ) (x : Rect)
    (hx : ∀ j, x (Fin.last d) j = 0) :
    logRectangleSize x ≤ Real.log (rectangleConstant m d) +
      (2 * (((d + 1 : ℕ) : ℝ))) * rootPos (alpha (blockPoint y x)) := by
  let R := rootPos (alpha (blockPoint y x))
  let D : ℝ := ((d + 1 : ℕ) : ℝ)
  let F : ℝ := (d + 1).factorial
  have hR := rootPos_nonneg (alpha (blockPoint y x))
  have hC := lt_of_lt_of_le zero_lt_one (rectangleConstant_one_le m d)
  have hsum : ∑ i, ∑ j, ‖x i j‖ ^ 2 ≤ D * (m : ℝ) * (F * Real.exp (D * R)) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin (d + 1), ∑ _j : Fin m, (F * Real.exp (D * R)) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (blockPoint_entry_le_roots y x hx i j) 2
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  apply Real.exp_le_exp.mp
  rw [logRectangleSize, Real.exp_log (by positivity), Real.exp_add, Real.exp_log hC]
  change _ ≤ rectangleConstant m d * Real.exp ((2 * D) * R)
  have hE : 1 ≤ Real.exp ((2 * D) * R) := Real.one_le_exp_iff.mpr
    (mul_nonneg (by positivity) hR)
  calc
    _ ≤ 1 + D * (m : ℝ) * (F * Real.exp (D * R)) ^ 2 := add_le_add le_rfl hsum
    _ = 1 + D * (m : ℝ) * F ^ 2 * Real.exp ((2 * D) * R) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    _ ≤ _ := by
      change _ ≤ (1 + D * (m : ℝ) * F ^ 2) * _
      rw [add_mul, one_mul]
      exact add_le_add hE le_rfl

private theorem sum_positive_blockPoint_le (y : Fin m → ℝ) (x : Rect)
    (hx : ∀ j, x (Fin.last d) j = 0) :
    (∑ j, max (y j) 0) ≤ (m : ℝ) *
      (Real.log (((m + d + 1 : ℕ) : ℝ)) + logRectangleSize x + rootPos (alpha (blockPoint y x))) := by
  let g := blockPoint y x
  let R := rootPos (alpha g)
  let B := Real.log (((m + d + 1 : ℕ) : ℝ))
  have hB : 0 ≤ B := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (m + d)))
  have hX := logRectangleSize_nonneg x
  have hR := rootPos_nonneg (alpha g)
  have hy (j : Fin m) : y j ≤ B + logRectangleSize x + R := by
    let i := j.castAdd (d + 1)
    have hi := neg_alpha_le_of_invCol g i (-y j + logRectangleSize x)
      (fun p => blockPoint_inv_leadingCol y x p j)
    have hlast : alpha g (Fin.last (m + d)) = 0 := blockPoint_last y x hx
    have hz := sub_last_le (alpha g) i
    rw [hlast, sub_zero] at hz
    change -alpha g i ≤ B + (-y j + logRectangleSize x) at hi
    change alpha g i ≤ R at hz
    linarith
  calc
    _ ≤ ∑ _j : Fin m, (B + logRectangleSize x + R) :=
      Finset.sum_le_sum fun j _ => max_le (hy j) (add_nonneg (add_nonneg hB hX) hR)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem lowerBlockLocalization_eq_blockPoint (y : Fin m → ℝ) (x : Matrix (Fin d) (Fin m) ℂ) :
    lowerBlockLocalization 1 (logTorus y) x 1 =
      blockPoint y (RectangularIwasawa.extendRectangle 1 x) := by
  have h := RectangularIwasawa.lowerBlockLocalization_reindex (c := 1) (logTorus y) x
  have hre := Langlands.RankinSelberg.reindex_finCongr_self
    (k := m + d + 1) (Nat.add_assoc m d 1) (lowerBlockLocalization 1 (logTorus y) x 1)
  exact hre.symm.trans h

private theorem exists_bounds_reindex (m d r : ℕ) (e : m + d = r) :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ (y : Fin m → ℝ) (x : Matrix (Fin d) (Fin m) ℂ),
      let g := GeneralLinear.reindex (finCongr (congrArg (· + 1) e))
        (lowerBlockLocalization 1 (logTorus y) x 1)
      (∑ i, |alpha g i|) ≤ ((r + 1 : ℕ) : ℝ) * (B + (∑ j, |y j|) + logRectangleSize x) ∧
        (∑ j, max (y j) 0) + logRectangleSize x ≤ K * (1 + rootPos (alpha g)) := by
  subst r
  let B := Real.log (((m + d + 1 : ℕ) : ℝ))
  let C := Real.log (rectangleConstant m d)
  let D : ℝ := 2 * (((d + 1 : ℕ) : ℝ))
  let K₀ := (m : ℝ) * B + ((m : ℝ) + 1) * C
  let K₁ := (m : ℝ) + ((m : ℝ) + 1) * D
  have hB : 0 ≤ B := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (m + d)))
  have hC : 0 ≤ C := Real.log_nonneg (rectangleConstant_one_le m d)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  refine ⟨B, K₀ + K₁, hB, add_nonneg hK₀ hK₁, fun y x => ?_⟩
  let X := RectangularIwasawa.extendRectangle 1 x
  have hx : ∀ j, X (Fin.last d) j = 0 := by
    intro j
    simp [X, RectangularIwasawa.extendRectangle, Fin.append_right_eq_snoc]
  have hsize : logRectangleSize X = logRectangleSize x := logRectangleSize_extend x
  dsimp only
  rw [Langlands.RankinSelberg.reindex_finCongr_self, lowerBlockLocalization_eq_blockPoint]
  rw [← hsize]
  change _ ∧ (∑ j, max (y j) 0) + logRectangleSize X ≤
    (K₀ + K₁) * (1 + rootPos (alpha (blockPoint y X)))
  refine ⟨blockPoint_length_le y X, ?_⟩
  let R := rootPos (alpha (blockPoint y X))
  have hR : 0 ≤ R := rootPos_nonneg _
  have hy : ∑ j, max (y j) 0 ≤ (m : ℝ) * (B + logRectangleSize X + R) :=
    sum_positive_blockPoint_le y X hx
  have hX : logRectangleSize X ≤ C + D * R := logRectangleSize_le_roots y X hx
  calc
    _ ≤ K₀ + K₁ * R := by
      have h := mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg (α := ℝ) m)
      dsimp only [K₀, K₁]
      nlinarith only [hy, hX, h]
    _ ≤ (K₀ + K₁) * (1 + R) := by
      rw [mul_add, mul_one]
      exact add_le_add (le_add_of_nonneg_right hK₁)
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK₀) hR)

end Block

/-- Logarithmic growth and positive-coordinate bounds on the exact three-block chart. -/
theorem exists_rectangularBounds {r t : ℕ} (h : t < r) :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ (y : Fin (t + 1) → ℝ)
      (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ),
      let g := ArchimedeanLocal.rectangularPoint h (logTorus y) x
      (∑ i, |alpha g i|) ≤ ((r + 1 : ℕ) : ℝ) * (B + (∑ j, |y j|) + logRectangleSize x) ∧
        (∑ j, max (y j) 0) + logRectangleSize x ≤ K * (1 + rootPos (alpha g)) :=
  exists_bounds_reindex (t + 1) (r - (t + 1)) r (Nat.add_sub_of_le (Nat.succ_le_of_lt h))

end Langlands.Global.RankinSelbergGlobal.ComplexLocalRectangularBounds

namespace Langlands.Global.RankinSelbergGlobal

open ComplexLocalIwasawa (alpha)
open ComplexLocalRectangularBounds (logRectangleSize)
open ComplexLocalWhittakerGauge (logTorus)
open RealConvergenceAnalysis (rootPos)

/-- In the exact complex rectangular chart, the sum of absolute Iwasawa logarithms is
controlled by the logarithmic sizes of the input diagonal and rectangle. The sum of the
positive input logarithms and the rectangular size is controlled by the positive simple roots. -/
def ComplexLocalRectangularBoundsStatement : Prop :=
  ∀ {r t : ℕ} (h : t < r),
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ (y : Fin (t + 1) → ℝ)
      (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ),
      let g := ArchimedeanLocal.rectangularPoint h (logTorus y) x
      (∑ i, |alpha g i|) ≤ ((r + 1 : ℕ) : ℝ) * (B + (∑ j, |y j|) + logRectangleSize x) ∧
        (∑ j, max (y j) 0) + logRectangleSize x ≤ K * (1 + rootPos (alpha g))

theorem complexLocalRectangularBounds : ComplexLocalRectangularBoundsStatement :=
  fun h => ComplexLocalRectangularBounds.exists_rectangularBounds h

end Langlands.Global.RankinSelbergGlobal
