import Langlands.Global.RankinSelberg.RealWhittakerGauge
import Langlands.Global.RankinSelberg.RealConvergenceAnalysis
import Langlands.Group.GL.Maps
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The Iwasawa bounds for the real Godement first-column integral -/

noncomputable section

open Langlands.GeneralLinear Langlands.Archimedean Matrix
open Langlands.Global.RankinSelbergGlobal.RealIwasawa
open Langlands.Global.RankinSelbergGlobal.RealConvergenceAnalysis
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "V" => (Fin (t + 1) → ℝ)
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ
local notation "E" => EuclideanSpace ℝ (Fin (t + 1))
local notation "F" => EuclideanSpace ℝ (Fin (t + 1) × Fin (t + 1))

/-- The simple-root Fourier frequency after changing the free Godement column. -/
def columnFrequency (h : G) : V :=
  (inverseTranspose (t + 1) ℝ h).val *ᵥ Pi.single (0 : Fin (t + 1)) 1

private theorem columnFrequency_apply (h : G) (i : Fin (t + 1)) :
    columnFrequency h i = (h⁻¹).val 0 i := by
  rw [columnFrequency, inverseTranspose_coe]
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The lower Whittaker coefficient uses this representative when the kernel's
lower translator is `h`. -/
def columnRepresentative (h : G) : G := weylLong (t + 1) ℝ * h⁻¹

private theorem abs_det_eq_one_of_sq (x : ℝ) (hx : x * x = 1) : |x| = 1 := by
  apply (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by decide : 2 ≠ 0)).mp
  rw [pow_two, ← abs_mul, hx, abs_one]

private theorem abs_det_weyl (d : ℕ) : |(weylLong d ℝ).val.det| = 1 := by
  apply abs_det_eq_one_of_sq
  rw [← Matrix.det_mul, ← Units.val_mul, weylLong_mul_self, Units.val_one, Matrix.det_one]

private theorem abs_det_orthogonal (k : unitaryCompact ℝ (t + 1)) : |k.val.val.det| = 1 := by
  apply abs_det_eq_one_of_sq
  have hk : k.val.val * k.val.val.transpose = 1 := by
    rw [← val_inv_of_mem k, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h := congrArg Matrix.det hk
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using h

/-- The sum of the logarithmic Iwasawa coordinates is the negative logarithm
of the absolute determinant of the lower translator. -/
theorem log_det_columnRepresentative (h : G) :
    Real.log |h.val.det| = -∑ i, alpha (columnRepresentative h) i := by
  let g := columnRepresentative h
  have hb : |g.val.det| = Real.exp (∑ i, alpha g i) := by
    conv_lhs => rw [← bpart_mul_kpart g]
    rw [Units.val_mul, Matrix.det_mul, abs_mul, abs_det_orthogonal, mul_one,
      Matrix.det_of_isUpperTriangular (isPosUpper_bpart g).1]
    simp_rw [← exp_alpha, ← Real.exp_sum, abs_of_pos (Real.exp_pos _)]
  have hg : |g.val.det| = |h.val.det|⁻¹ := by
    change |(weylLong (t + 1) ℝ * h⁻¹).val.det| = _
    rw [Units.val_mul, Matrix.det_mul, abs_mul, abs_det_weyl, one_mul,
      ← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val, abs_inv]
    rfl
  rw [← neg_neg (Real.log |h.val.det|), ← Real.log_inv, ← hg, hb, Real.log_exp]

private theorem bpart_inv_alpha (g : G) (i : Fin (t + 1)) :
    (bpart g)⁻¹ i i = Real.exp (-alpha g i) := by
  have hb := isPosUpper_bpart g
  have h := congrArg (fun x : G => x i i) (mul_inv_cancel (bpart g))
  change ((bpart g).val * ((bpart g)⁻¹).val) i i = (1 : M) i i at h
  rw [upper_mul_diag hb.1 (isPosUpper_inv hb).1, Matrix.one_apply_eq] at h
  rw [Real.exp_neg, exp_alpha]
  exact eq_inv_of_mul_eq_one_right h

private theorem exp_neg_alpha_columnRepresentative (h : G) (i : Fin (t + 1)) :
    Real.exp (-alpha (columnRepresentative h) i) ≤
      (t + 1 : ℕ) * ‖(WithLp.toLp 2 (Function.uncurry h.val) : F)‖ := by
  let g := columnRepresentative h
  let k := kpart g
  have hInv : (bpart g)⁻¹ = k.val * (h * weylLong (t + 1) ℝ) := by
    simp only [bpart, g, columnRepresentative, _root_.mul_inv_rev, inv_inv, weylLong_inv, k]
  rw [← bpart_inv_alpha, hInv]
  change (k.val.val * (h * weylLong (t + 1) ℝ).val) i i ≤ _
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ j : Fin (t + 1), |k.val.val i j * (h * weylLong (t + 1) ℝ) j i| :=
      Finset.sum_le_sum fun j _ => le_abs_self _
    _ ≤ ∑ _j : Fin (t + 1), ‖(WithLp.toLp 2 (Function.uncurry h.val) : F)‖ := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, mul_weylLong_entry]
      have hk := RealWhittakerGauge.abs_unitary_entry_le k i j
      have hh : |h.val j i.rev| ≤ ‖(WithLp.toLp 2 (Function.uncurry h.val) : F)‖ := by
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le (WithLp.toLp 2 (Function.uncurry h.val) : F) (j, i.rev)
      exact (mul_le_mul hk hh (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem exp_last_alpha_columnRepresentative (h : G) :
    Real.exp (alpha (columnRepresentative h) (Fin.last t)) ≤
      (t + 1 : ℕ) * ‖(WithLp.toLp 2 (columnFrequency h) : E)‖ := by
  let g := columnRepresentative h
  let i := Fin.last t
  let k := kpart g
  have hRow (j : Fin (t + 1)) : g i j = columnFrequency h j := by
    change (weylLong (t + 1) ℝ * h⁻¹) (Fin.last t) j = _
    rw [weylLong_mul_entry, columnFrequency_apply]
    simp
  rw [exp_alpha]
  change (g.val * (k.val⁻¹).val) i i ≤ _
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ j : Fin (t + 1), |g i j * (k.val⁻¹) j i| :=
      Finset.sum_le_sum fun j _ => le_abs_self _
    _ ≤ ∑ _j : Fin (t + 1), ‖(WithLp.toLp 2 (columnFrequency h) : E)‖ := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, hRow]
      have hk := RealWhittakerGauge.abs_unitary_inv_entry_le k j i
      have hh : |columnFrequency h j| ≤ ‖(WithLp.toLp 2 (columnFrequency h) : E)‖ := by
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le (WithLp.toLp 2 (columnFrequency h) : E) j
      exact (mul_le_mul hh hk (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The matrix norm, Fourier frequency norm, and positive simple-root
coordinates control the sum of the absolute logarithmic Iwasawa coordinates. -/
theorem sum_abs_alpha_columnRepresentative (h : G) :
    let y := alpha (columnRepresentative h)
    ∑ i, |y i| ≤ (t + 1 : ℕ) *
      (Real.log ((t + 1 : ℕ) * (1 + ‖(WithLp.toLp 2 (Function.uncurry h.val) : F)‖)) +
        Real.log ((t + 1 : ℕ) * (1 + ‖(WithLp.toLp 2 (columnFrequency h) : E)‖)) + rootPos y) := by
  let y := alpha (columnRepresentative h)
  let A := (t + 1 : ℕ) * (1 + ‖(WithLp.toLp 2 (Function.uncurry h.val) : F)‖)
  let B := (t + 1 : ℕ) * (1 + ‖(WithLp.toLp 2 (columnFrequency h) : E)‖)
  have hm : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos t
  have hA : (1 : ℝ) ≤ A := one_le_mul_of_one_le_of_one_le hm (le_add_of_nonneg_right (norm_nonneg _))
  have hB : (1 : ℝ) ≤ B := one_le_mul_of_one_le_of_one_le hm (le_add_of_nonneg_right (norm_nonneg _))
  have hLower (i : Fin (t + 1)) : -y i ≤ Real.log A := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log (lt_of_lt_of_le zero_lt_one hA)]
    exact (exp_neg_alpha_columnRepresentative h i).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
  have hLast : y (Fin.last t) ≤ Real.log B := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log (lt_of_lt_of_le zero_lt_one hB)]
    exact (exp_last_alpha_columnRepresentative h).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
  change ∑ i, |y i| ≤ (t + 1 : ℕ) * (Real.log A + Real.log B + rootPos y)
  calc
    _ ≤ ∑ _i : Fin (t + 1), (Real.log A + Real.log B + rootPos y) := by
      refine Finset.sum_le_sum fun i _ => abs_le.mpr ⟨?_, ?_⟩
      · linarith [hLower i, Real.log_nonneg hB, rootPos_nonneg y]
      · linarith [sub_last_le y i, hLast, Real.log_nonneg hA]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The determinant and Iwasawa estimate used for the real column kernel. -/
def RealGodementColumnBoundsStatement : Prop :=
  ∀ (t : ℕ) (h : Langlands.GeneralLinear (t + 1) ℝ),
    let y := alpha (columnRepresentative h)
    Real.log |h.val.det| = -∑ i, y i ∧
      ∑ i, |y i| ≤ (t + 1 : ℕ) *
        (Real.log ((t + 1 : ℕ) * (1 + ‖(WithLp.toLp 2 (Function.uncurry h.val) :
          EuclideanSpace ℝ (Fin (t + 1) × Fin (t + 1)))‖)) +
          Real.log ((t + 1 : ℕ) * (1 + ‖(WithLp.toLp 2 (columnFrequency h) :
            EuclideanSpace ℝ (Fin (t + 1)))‖)) + rootPos y)

theorem realGodementColumnBounds : RealGodementColumnBoundsStatement := by
  intro t h
  exact ⟨log_det_columnRepresentative h, sum_abs_alpha_columnRepresentative h⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
