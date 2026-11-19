import Langlands.Global.RankinSelberg.RealIwasawaBounds
import Langlands.Global.RankinSelberg.RealConvergenceAnalysis
import Langlands.Group.GL.LowerBlockLocalizationCoordinates

/-! # Toral Iwasawa coordinates of `[[g,0,0],[x,1,0],[0,0,1]]` over `ℝ` -/

noncomputable section

open Matrix

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealRectangularIwasawa

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (lowerBlockLocalization lowerBlockFirst lowerBlockMiddle
  lowerBlockLast lowerTriangularSubgroup)
open RealIwasawa RealConvergenceAnalysis

variable {a d : ℕ}

/-- The matrix `[[g,0,0],[x,1_d,0],[0,0,1]]`. -/
abbrev rect (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) :
    Langlands.GeneralLinear (a + d + 1) ℝ :=
  lowerBlockLocalization 1 g x 1

theorem sum_split (f : Fin (a + d + 1) → ℝ) :
    ∑ i, f i = ∑ j : Fin a, f (lowerBlockFirst d 1 j) + ∑ l : Fin d, f (lowerBlockMiddle a 1 l) +
      f (lowerBlockLast a d 0) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]
  rfl

theorem rect_inv (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) :
    (rect g x)⁻¹ = lowerBlockLocalization 1 g⁻¹
      (-(x * ((g⁻¹ : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ))) 1 := by
  rw [rect, Langlands.GeneralLinear.lowerBlockLocalization_inv, inv_one]
  congr 2
  simp

/-! ### Rows of `rect g x` and columns of its inverse -/

theorem rowsq_first (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) (j : Fin a) :
    ∑ q, (((rect g x : Langlands.GeneralLinear (a + d + 1) ℝ) :
      Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ) (lowerBlockFirst d 1 j) q) ^ 2 =
      ∑ q, ((g : Matrix (Fin a) (Fin a) ℝ) j q) ^ 2 := by
  rw [sum_split]
  simp

theorem rowsq_middle (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) (l : Fin d) :
    ∑ q, (((rect g x : Langlands.GeneralLinear (a + d + 1) ℝ) :
      Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ) (lowerBlockMiddle a 1 l) q) ^ 2 =
      ∑ q, (x l q) ^ 2 + 1 := by
  rw [sum_split]
  simp [Matrix.one_apply]

theorem rowsq_last (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) :
    ∑ q, (((rect g x : Langlands.GeneralLinear (a + d + 1) ℝ) :
      Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ) (lowerBlockLast a d 0) q) ^ 2 = 1 := by
  rw [sum_split]
  simp

theorem colsq_first (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) (j : Fin a) :
    ∑ p, ((((rect g x)⁻¹ : Langlands.GeneralLinear (a + d + 1) ℝ) :
      Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ) p (lowerBlockFirst d 1 j)) ^ 2 =
      ∑ p, (((g⁻¹ : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) p j) ^ 2 +
        ∑ l, ((x * ((g⁻¹ : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ)) l j) ^ 2 := by
  rw [rect_inv, sum_split]
  simp

theorem colsq_middle (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) (l : Fin d) :
    ∑ p, ((((rect g x)⁻¹ : Langlands.GeneralLinear (a + d + 1) ℝ) :
      Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ) p (lowerBlockMiddle a 1 l)) ^ 2 = 1 := by
  rw [rect_inv, sum_split]
  simp [Matrix.one_apply]

theorem colsq_last (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) :
    ∑ p, ((((rect g x)⁻¹ : Langlands.GeneralLinear (a + d + 1) ℝ) :
      Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ) p (lowerBlockLast a d 0)) ^ 2 = 1 := by
  rw [rect_inv, sum_split]
  simp

/-- The Gram matrix of the first `a` columns of `(rect g x)⁻¹` is `ᵗg⁻¹ (1 + ᵗx x) g⁻¹`. -/
theorem gram_first (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) :
    ((((rect g x)⁻¹ : Langlands.GeneralLinear (a + d + 1) ℝ) :
        Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ).submatrix id (lowerBlockFirst d 1))ᵀ *
      ((((rect g x)⁻¹ : Langlands.GeneralLinear (a + d + 1) ℝ) :
        Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ).submatrix id (lowerBlockFirst d 1)) =
      ((g⁻¹ : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ)ᵀ * (1 + xᵀ * x) *
        ((g⁻¹ : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) := by
  set G := ((g⁻¹ : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) with hG
  have e : Gᵀ * (1 + xᵀ * x) * G = Gᵀ * G + (x * G)ᵀ * (x * G) := by
    simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  rw [e]
  ext j j'
  rw [Matrix.mul_apply, sum_split, rect_inv]
  simp [Matrix.mul_apply, hG]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-- `exp(−2 ∑_(j<a) α_j(rect g x)) = det(g)⁻² det(1 + ᵗx x)`. -/
theorem exp_sum_first (g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) :
    Real.exp (-(2 * ∑ j : Fin a, alpha (rect g x) (lowerBlockFirst d 1 j))) =
      Matrix.det ((g⁻¹ : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) ^ 2 *
        Matrix.det (1 + xᵀ * x) := by
  set C := (((rect g x)⁻¹ : Langlands.GeneralLinear (a + d + 1) ℝ) :
    Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ).submatrix id (lowerBlockFirst d 1) with hC
  have h : Real.exp (-(2 * ∑ j : Fin a, alpha (rect g x) (lowerBlockFirst d 1 j))) =
      Matrix.det (Cᵀ * C) := (det_gram_inv_cols (a := a) (e := d + 1) (rect g x)).symm
  rw [h, hC, gram_first, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-! ### Specialization to `g = torus y · k` -/

theorem torus_mul_apply (y : Fin a → ℝ) (k : unitaryCompact ℝ a) (p q : Fin a) :
    ((torus y * (k : Langlands.GeneralLinear a ℝ) : Langlands.GeneralLinear a ℝ) :
      Matrix (Fin a) (Fin a) ℝ) p q =
      Real.exp (y p) * ((k : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) p q := by
  rw [Units.val_mul, torus_val, Matrix.diagonal_mul]

theorem torus_mul_inv_apply (y : Fin a → ℝ) (k : unitaryCompact ℝ a) (p q : Fin a) :
    (((torus y * (k : Langlands.GeneralLinear a ℝ))⁻¹ : Langlands.GeneralLinear a ℝ) :
      Matrix (Fin a) (Fin a) ℝ) p q =
      ((k : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) q p * Real.exp (-y q) := by
  have h : (((torus y * (k : Langlands.GeneralLinear a ℝ))⁻¹ : Langlands.GeneralLinear a ℝ) :
      Matrix (Fin a) (Fin a) ℝ) =
      ((k : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ)ᵀ *
        Matrix.diagonal fun i => Real.exp ((-y) i) := by
    rw [_root_.mul_inv_rev, ← torus_neg, Units.val_mul, torus_val, val_inv_of_mem]
  rw [h, Matrix.mul_diagonal, Matrix.transpose_apply]
  rfl

theorem unitary_row_sq (k : unitaryCompact ℝ a) (j : Fin a) :
    ∑ q, (((k : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) j q) ^ 2 = 1 := by
  have h := congrFun (congrFun (unitary_mul_transpose k) j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h]
  simp [sq]

theorem rowsq_torus (y : Fin a → ℝ) (k : unitaryCompact ℝ a) (j : Fin a) :
    ∑ q, (((torus y * (k : Langlands.GeneralLinear a ℝ) : Langlands.GeneralLinear a ℝ) :
      Matrix (Fin a) (Fin a) ℝ) j q) ^ 2 = Real.exp (2 * y j) := by
  simp_rw [torus_mul_apply, mul_pow, ← Finset.mul_sum, unitary_row_sq, mul_one, ← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem colsq_torus (y : Fin a → ℝ) (k : unitaryCompact ℝ a) (j : Fin a) :
    ∑ p, ((((torus y * (k : Langlands.GeneralLinear a ℝ))⁻¹ : Langlands.GeneralLinear a ℝ) :
      Matrix (Fin a) (Fin a) ℝ) p j) ^ 2 = Real.exp (-(2 * y j)) := by
  simp_rw [torus_mul_inv_apply, mul_pow, ← Finset.sum_mul, unitary_row_sq, one_mul,
    ← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem sq_det_torus_mul_inv (y : Fin a → ℝ) (k : unitaryCompact ℝ a) :
    Matrix.det (((torus y * (k : Langlands.GeneralLinear a ℝ))⁻¹ : Langlands.GeneralLinear a ℝ) :
      Matrix (Fin a) (Fin a) ℝ) ^ 2 = Real.exp (-(2 * ∑ j, y j)) := by
  have hk : Matrix.det ((k : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) ^ 2 = 1 := by
    have hU : ((k : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) ∈
        Matrix.unitaryGroup (Fin a) ℝ := k.2
    have h1 := Matrix.det_of_mem_unitary hU
    have h2 := CStarRing.norm_of_mem_unitary h1
    rw [Real.norm_eq_abs] at h2
    rw [← sq_abs, h2, one_pow]
  have hg : Matrix.det ((torus y * (k : Langlands.GeneralLinear a ℝ) :
      Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) ^ 2 =
      Real.exp (2 * ∑ j, y j) := by
    rw [Units.val_mul, Matrix.det_mul, torus_val, Matrix.det_diagonal, mul_pow, hk, mul_one,
      ← Real.exp_sum, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_pow,
    hg, ← Real.exp_neg]

/-- Cauchy–Schwarz for `x v`. -/
theorem sum_sq_mul_le (x : Matrix (Fin d) (Fin a) ℝ) (v : Fin a → ℝ) :
    ∑ l, (∑ p, x l p * v p) ^ 2 ≤ (∑ l, ∑ p, x l p ^ 2) * ∑ p, v p ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun l _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ### The estimates -/

/-- `S = ∑ x_(lp)²`, the squared Frobenius norm. -/
def frob (x : Matrix (Fin d) (Fin a) ℝ) : ℝ := ∑ l, ∑ p, x l p ^ 2

theorem frob_nonneg (x : Matrix (Fin d) (Fin a) ℝ) : 0 ≤ frob x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

section Estimates

variable (y : Fin a → ℝ) (k : unitaryCompact ℝ a) (x : Matrix (Fin d) (Fin a) ℝ)

/-- The coordinate `z = α(rect (torus y · k) x)`. -/
abbrev zc : Fin (a + d + 1) → ℝ := alpha (rect (torus y * (k : Langlands.GeneralLinear a ℝ)) x)

theorem first_upper (j : Fin a) : 2 * zc y k x (lowerBlockFirst d 1 j) ≤ 2 * y j := by
  have h := exp_two_mul_alpha_le (rect (torus y * (k : Langlands.GeneralLinear a ℝ)) x)
    (lowerBlockFirst d 1 j)
  rw [rowsq_first, rowsq_torus] at h
  exact Real.exp_le_exp.mp h

theorem first_lower (j : Fin a) :
    -(2 * zc y k x (lowerBlockFirst d 1 j)) ≤ -(2 * y j) + Real.log (1 + frob x) := by
  have h := exp_neg_two_mul_alpha_le (rect (torus y * (k : Langlands.GeneralLinear a ℝ)) x)
    (lowerBlockFirst d 1 j)
  rw [colsq_first, colsq_torus] at h
  have hcs := sum_sq_mul_le x (fun p => (((torus y * (k : Langlands.GeneralLinear a ℝ))⁻¹ :
    Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) p j)
  rw [colsq_torus] at hcs
  have h2 : Real.exp (-(2 * zc y k x (lowerBlockFirst d 1 j))) ≤
      Real.exp (-(2 * y j)) * (1 + frob x) := by
    refine h.trans ?_
    have e : ∑ l, ((x * (((torus y * (k : Langlands.GeneralLinear a ℝ))⁻¹ :
        Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ)) l j) ^ 2 =
        ∑ l, (∑ p, x l p * (((torus y * (k : Langlands.GeneralLinear a ℝ))⁻¹ :
          Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) p j) ^ 2 := by
      simp [Matrix.mul_apply]
    rw [e]
    unfold frob
    nlinarith [Real.exp_pos (-(2 * y j))]
  have hpos : 0 < 1 + frob x := by linarith [frob_nonneg x]
  rw [← Real.exp_log hpos, ← Real.exp_add] at h2
  exact Real.exp_le_exp.mp h2

theorem middle_upper (l : Fin d) :
    2 * zc y k x (lowerBlockMiddle a 1 l) ≤ Real.log (1 + frob x) := by
  have h := exp_two_mul_alpha_le (rect (torus y * (k : Langlands.GeneralLinear a ℝ)) x)
    (lowerBlockMiddle a 1 l)
  rw [rowsq_middle] at h
  have hle : ∑ q, x l q ^ 2 + 1 ≤ 1 + frob x := by
    unfold frob
    have := Finset.single_le_sum (f := fun l => ∑ p, x l p ^ 2)
      (fun l _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ l)
    linarith
  have hpos : 0 < 1 + frob x := by linarith [frob_nonneg x]
  rw [← Real.exp_log hpos] at hle
  exact Real.exp_le_exp.mp (h.trans hle)

theorem middle_lower (l : Fin d) : 0 ≤ zc y k x (lowerBlockMiddle a 1 l) := by
  have h := exp_neg_two_mul_alpha_le (rect (torus y * (k : Langlands.GeneralLinear a ℝ)) x)
    (lowerBlockMiddle a 1 l)
  rw [colsq_middle, ← Real.exp_zero] at h
  linarith [Real.exp_le_exp.mp h]

theorem last_eq : zc y k x (lowerBlockLast a d 0) = 0 := by
  have h1 := exp_two_mul_alpha_le (rect (torus y * (k : Langlands.GeneralLinear a ℝ)) x)
    (lowerBlockLast a d 0)
  have h2 := exp_neg_two_mul_alpha_le (rect (torus y * (k : Langlands.GeneralLinear a ℝ)) x)
    (lowerBlockLast a d 0)
  rw [rowsq_last, ← Real.exp_zero] at h1
  rw [colsq_last, ← Real.exp_zero] at h2
  have := Real.exp_le_exp.mp h1
  have := Real.exp_le_exp.mp h2
  linarith

theorem sum_first_le :
    2 * ∑ j : Fin a, zc y k x (lowerBlockFirst d 1 j) ≤ 2 * ∑ j, y j - Real.log (1 + frob x) := by
  have h := exp_sum_first (torus y * (k : Langlands.GeneralLinear a ℝ)) x
  rw [sq_det_torus_mul_inv] at h
  have hdet := RealIwasawa.one_add_sum_sq_le_det x
  have hpos : 0 < 1 + frob x := by linarith [frob_nonneg x]
  have h2 : Real.exp (-(2 * ∑ j, y j) + Real.log (1 + frob x)) ≤
      Real.exp (-(2 * ∑ j : Fin a, zc y k x (lowerBlockFirst d 1 j))) := by
    rw [h, Real.exp_add, Real.exp_log hpos]
    unfold frob
    exact mul_le_mul_of_nonneg_left hdet (Real.exp_pos _).le
  linarith [Real.exp_le_exp.mp h2]

theorem sum_all : ∑ i, zc y k x i = ∑ j, y j := by
  rw [← log_abs_det_eq_sum_alpha, Langlands.GeneralLinear.det_lowerBlockLocalization]
  have hk : |Matrix.det ((k : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ)| = 1 := by
    have hU : ((k : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) ∈
        Matrix.unitaryGroup (Fin a) ℝ := k.2
    have h1 := Matrix.det_of_mem_unitary hU
    have h2 := CStarRing.norm_of_mem_unitary h1
    rwa [Real.norm_eq_abs] at h2
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.det_one, mul_one]
  rw [Units.val_mul, Matrix.det_mul, torus_val, Matrix.det_diagonal, abs_mul, hk, mul_one,
    ← Real.exp_sum, abs_of_pos (Real.exp_pos _), Real.log_exp]

/-- **Growth.** `∑_i |z_i| ≤ ∑_j |y_j| + (a + d) log(1 + S)`. -/
theorem sum_abs_le :
    ∑ i, |zc y k x i| ≤ ∑ j, |y j| + ((a : ℝ) + d) * Real.log (1 + frob x) := by
  have hΛ : 0 ≤ Real.log (1 + frob x) := Real.log_nonneg (by linarith [frob_nonneg x])
  rw [sum_split, last_eq, abs_zero, add_zero]
  have h1 : ∑ j : Fin a, |zc y k x (lowerBlockFirst d 1 j)| ≤
      ∑ j : Fin a, (|y j| + Real.log (1 + frob x)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hu := first_upper y k x j
    have hl := first_lower y k x j
    rw [abs_le]
    constructor <;> cases abs_cases (y j) <;> linarith
  have h2 : ∑ l : Fin d, |zc y k x (lowerBlockMiddle a 1 l)| ≤
      ∑ _l : Fin d, Real.log (1 + frob x) := by
    refine Finset.sum_le_sum fun l _ => ?_
    have hu := middle_upper y k x l
    have hl := middle_lower y k x l
    rw [abs_of_nonneg hl]
    linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1 h2 ⊢
  linarith

/-- **Decay.** `∑_j max(y_j, 0) + a log(1 + S) / 2 ≤ (a + 2ad) · rootPos z`. -/
theorem decay_le :
    ∑ j, max (y j) 0 + (a : ℝ) * Real.log (1 + frob x) / 2 ≤
      ((a : ℝ) + 2 * a * d) * rootPos (zc y k x) := by
  set z := zc y k x with hz
  have hlast : z (Fin.last (a + d)) = 0 := last_eq y k x
  have hle : ∀ i, z i ≤ rootPos z := by
    intro i
    have := sub_last_le z i
    rw [hlast, sub_zero] at this
    exact this
  have hR := rootPos_nonneg z
  have hΛ : 0 ≤ Real.log (1 + frob x) := Real.log_nonneg (by linarith [frob_nonneg x])
  -- first block
  have h1 : ∑ j : Fin a, max (y j) 0 ≤
      ∑ j : Fin a, (rootPos z + Real.log (1 + frob x) / 2) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hl := first_lower y k x j
    have hz' := hle (lowerBlockFirst d 1 j)
    rw [← hz] at hl
    exact max_le (by linarith) (by linarith)
  -- middle block
  have h2 : Real.log (1 + frob x) / 2 ≤ ∑ l : Fin d, rootPos z := by
    have hs := sum_all y k x
    have hf := sum_first_le y k x
    rw [sum_split, last_eq, add_zero] at hs
    rw [← hz] at hs hf
    have : ∑ l : Fin d, z (lowerBlockMiddle a 1 l) ≤ ∑ l : Fin d, rootPos z :=
      Finset.sum_le_sum fun l _ => hle _
    linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1 h2 ⊢
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith

end Estimates

end Langlands.Global.RankinSelbergGlobal.RealRectangularIwasawa
