import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-! # Real similarity descends from complexification -/

noncomputable section

open Matrix

set_option autoImplicit false

namespace Langlands

variable {n : ℕ}

local notation "RMat" => Matrix (Fin n) (Fin n) ℝ
local notation "CMat" => Matrix (Fin n) (Fin n) ℂ

/-- Entrywise inclusion gives the square matrix ring homomorphism from reals to complexes. -/
def realMatrixComplexification (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ :=
  Complex.ofRealHom.mapMatrix

@[simp]
theorem realMatrixComplexification_apply (A : RMat) (i j : Fin n) :
    realMatrixComplexification n A i j = (A i j : ℂ) := rfl

theorem realMatrixComplexification_injective (n : ℕ) :
    Function.Injective (realMatrixComplexification n) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h)

theorem continuous_realMatrixComplexification (n : ℕ) :
    Continuous (realMatrixComplexification n) :=
  continuous_id.matrix_map Complex.continuous_ofReal

theorem realMatrixComplexification_transpose (A : RMat) :
    realMatrixComplexification n Aᵀ = (realMatrixComplexification n A)ᵀ := rfl

/-- An invertible intertwiner between complexifications of real matrices gives an invertible
real intertwiner. Its real and imaginary parts define a real linear pencil with nonzero
determinant polynomial. -/
theorem exists_realUnitIntertwiner_of_complex (A B : RMat) (u : CMatˣ)
    (h : (u : CMat) * realMatrixComplexification n A = realMatrixComplexification n B * (u : CMat)) :
    ∃ v : RMatˣ, (v : RMat) * A = B * (v : RMat) := by
  let R : RMat := (u : CMat).map Complex.re
  let I : RMat := (u : CMat).map Complex.im
  have hR : R * A = B * R := by
    ext i j
    have hij := congrArg (fun M : CMat => Complex.reCLM (M i j)) h
    simpa only [Matrix.mul_apply, realMatrixComplexification_apply, map_sum, Complex.reCLM_apply,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      Matrix.map_apply, R] using hij
  have hI : I * A = B * I := by
    ext i j
    have hij := congrArg (fun M : CMat => Complex.imCLM (M i j)) h
    simpa only [Matrix.mul_apply, realMatrixComplexification_apply, map_sum, Complex.imCLM_apply,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, zero_add,
      Matrix.map_apply, I] using hij
  let P : Matrix (Fin n) (Fin n) (Polynomial ℝ) :=
    Polynomial.C.mapMatrix R + (Polynomial.X : Polynomial ℝ) • Polynomial.C.mapMatrix I
  let p := P.det
  have hline {K : Type} [CommRing K] (f : ℝ →+* K) (t : K) :
      (Polynomial.eval₂RingHom f t).mapMatrix P = f.mapMatrix R + t • f.mapMatrix I := by
    ext i j
    simp [P, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact mul_comm _ _
  have hcomplex : Complex.ofRealHom.mapMatrix R + Complex.I • Complex.ofRealHom.mapMatrix I =
      (u : CMat) := by
    ext i j
    change ((u : CMat) i j).re + Complex.I * (((u : CMat) i j).im : ℂ) = (u : CMat) i j
    rw [mul_comm Complex.I, Complex.re_add_im]
  have hEval : Polynomial.eval₂RingHom Complex.ofRealHom Complex.I p = (u : CMat).det := by
    change Polynomial.eval₂RingHom Complex.ofRealHom Complex.I P.det = _
    rw [RingHom.map_det, hline, hcomplex]
  have hp : p ≠ 0 := by
    intro hp0
    apply (isUnits_det_units u).ne_zero
    rw [← hEval, hp0, map_zero]
  obtain ⟨t, ht⟩ := (Polynomial.eventually_eval_ne_zero_cofinite hp).exists
  have hEvalReal : p.eval t = (R + t • I).det := by
    change Polynomial.eval₂RingHom (RingHom.id ℝ) t P.det = _
    rw [RingHom.map_det, hline]
    rfl
  have hu : IsUnit (R + t • I) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hEvalReal ▸ ht))
  obtain ⟨v, hv⟩ := hu
  refine ⟨v, ?_⟩
  rw [hv, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, hR, hI]

end Langlands
