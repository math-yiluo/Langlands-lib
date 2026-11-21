import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # The real trace contraction for real and complex matrix spaces -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix

namespace Langlands.Archimedean

universe uF uV

variable (F : Type uF) [RCLike F] (n : ℕ)

/-- The real trace pairing on the real matrix Lie algebra. -/
def matrixRealTracePairing (X Y : Matrix (Fin n) (Fin n) F) : ℝ :=
  RCLike.re (X * Y).trace

/-- The real and imaginary matrix units, with the imaginary family zero over `ℝ`. -/
def matrixTraceUnit (i : Fin n × Fin n × Bool) : Matrix (Fin n) (Fin n) F :=
  Matrix.single i.1 i.2.1 (if i.2.2 then RCLike.I else 1)

/-- The transposed units and their negative imaginary counterparts. -/
def matrixTraceDualUnit (i : Fin n × Fin n × Bool) : Matrix (Fin n) (Fin n) F :=
  Matrix.single i.2.1 i.1 (if i.2.2 then -RCLike.I else 1)

theorem matrixRealTracePairing_units_conj (g : (Matrix (Fin n) (Fin n) F)ˣ)
    (X Y : Matrix (Fin n) (Fin n) F) :
    matrixRealTracePairing F n (g.val * X * g⁻¹.val) (g.val * Y * g⁻¹.val) =
      matrixRealTracePairing F n X Y := by
  have h : (g.val * X * g⁻¹.val) * (g.val * Y * g⁻¹.val) =
      g.val * (X * Y) * g⁻¹.val := by simp [mul_assoc]
  rw [matrixRealTracePairing, h, Matrix.trace_units_conj]
  rfl

theorem matrixRealTracePairing_transpose (X Y : Matrix (Fin n) (Fin n) F) :
    matrixRealTracePairing F n X.transpose Y.transpose = matrixRealTracePairing F n X Y := by
  rw [matrixRealTracePairing, ← Matrix.transpose_mul, Matrix.trace_transpose,
    Matrix.trace_mul_comm]
  rfl

/-- Reconstruct a matrix using its real trace pairings against the dual family. -/
theorem sum_matrixTraceDualUnit_smul (X : Matrix (Fin n) (Fin n) F) :
    X = ∑ i, matrixRealTracePairing F n X (matrixTraceDualUnit F n i) • matrixTraceUnit F n i := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [matrixTraceUnit, matrixTraceDualUnit, matrixRealTracePairing,
    Bool.false_eq_true, ite_false, ite_true, Matrix.trace_mul_single, op_smul_eq_mul,
    mul_one, mul_neg, map_neg, Matrix.smul_single, RCLike.real_smul_eq_coe_mul,
    ← Matrix.single_add]
  rw [mul_comm (X i j) RCLike.I, RCLike.I_mul_re]
  apply congrArg (Matrix.single i j)
  simpa only [RCLike.ofReal_neg, neg_neg, add_comm] using (RCLike.re_add_im (X i j)).symm

/-- The reverse reconstruction exchanges the two trace families. -/
theorem sum_matrixTraceUnit_smul (X : Matrix (Fin n) (Fin n) F) :
    X = ∑ i, matrixRealTracePairing F n (matrixTraceUnit F n i) X • matrixTraceDualUnit F n i := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [matrixTraceUnit, matrixTraceDualUnit, matrixRealTracePairing,
    Bool.false_eq_true, ite_false, ite_true, Matrix.trace_single_mul, smul_eq_mul,
    one_mul, Matrix.smul_single, RCLike.real_smul_eq_coe_mul, RCLike.I_mul_re,
    RCLike.ofReal_neg, neg_mul_neg, ← Matrix.single_add]
  rw [mul_one, add_comm, RCLike.re_add_im]

variable {V : Type uV} [AddCommGroup V] [Module ℝ V]

/-- A bilinear contraction against the two trace families is unchanged
by every real linear equivalence preserving the real trace pairing. -/
theorem sum_matrixTraceContraction_invariant
    (e : Matrix (Fin n) (Fin n) F ≃ₗ[ℝ] Matrix (Fin n) (Fin n) F)
    (he : ∀ X Y, matrixRealTracePairing F n (e X) (e Y) = matrixRealTracePairing F n X Y)
    (B : Matrix (Fin n) (Fin n) F →ₗ[ℝ] Matrix (Fin n) (Fin n) F →ₗ[ℝ] V) :
    (∑ i, B (e (matrixTraceUnit F n i)) (e (matrixTraceDualUnit F n i))) =
      ∑ i, B (matrixTraceUnit F n i) (matrixTraceDualUnit F n i) := by
  let b := matrixTraceUnit F n
  let d := matrixTraceDualUnit F n
  let P := matrixRealTracePairing F n
  change (∑ i, B (e (b i)) (e (d i))) = ∑ i, B (b i) (d i)
  have hsum (i : Fin n × Fin n × Bool) :
      B (e (b i)) (e (d i)) = ∑ j, P (e (b i)) (d j) • B (b j) (e (d i)) := by
    have h := congrArg (fun z => B z (e (d i))) (sum_matrixTraceDualUnit_smul F n (e (b i)))
    simpa only [b, d, P, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] using h
  have hcoeff (i j : Fin n × Fin n × Bool) :
      P (e (b i)) (d j) = P (b i) (e.symm (d j)) := by
    calc
      _ = P (e (b i)) (e (e.symm (d j))) := by rw [e.apply_symm_apply]
      _ = _ := he _ _
  simp_rw [hsum, hcoeff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  let L := (B (b j)).comp e.toLinearMap
  have hj := congrArg L (sum_matrixTraceUnit_smul F n (e.symm (d j)))
  simpa only [L, b, d, P, map_sum, map_smul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hj.symm

/-- Exchanging the two arguments leaves the trace contraction unchanged. -/
theorem sum_matrixTraceContraction_swap
    (B : Matrix (Fin n) (Fin n) F →ₗ[ℝ] Matrix (Fin n) (Fin n) F →ₗ[ℝ] V) :
    (∑ i, B (matrixTraceDualUnit F n i) (matrixTraceUnit F n i)) =
      ∑ i, B (matrixTraceUnit F n i) (matrixTraceDualUnit F n i) := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [matrixTraceDualUnit, matrixTraceUnit, ← Matrix.single_neg]

end Langlands.Archimedean
