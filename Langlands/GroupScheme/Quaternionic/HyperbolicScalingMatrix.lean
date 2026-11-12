import Langlands.GroupScheme.Quaternionic.HyperbolicScaling
import Langlands.GroupScheme.Quaternionic.QuadraticValueExt
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Matrix realization of the hyperbolic scaling action -/

noncomputable section

universe u v w

open scoped Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- The rank-one row-action matrix projecting to `D x` along the polar coordinate of `y`. -/
def hyperbolicLineMatrix (q : σ.QuadraticForms n) (x y : n → D) : Matrix n n D :=
  ((σ.polarFunctional q y).smulRight x).toMatrixRight'

@[simp] theorem vecMul_hyperbolicLineMatrix (q : σ.QuadraticForms n) (x y z : n → D) :
    z ᵥ* σ.hyperbolicLineMatrix q x y = σ.sesqForm (σ.polar q) z y • x := by
  exact congrArg (fun f : (n → D) →ₗ[D] (n → D) => f z)
    (LinearMap.toMatrixRight'.symm_apply_apply ((σ.polarFunctional q y).smulRight x))

/-- The Laurent-scalar formula for the hyperbolic scaling matrix. -/
def hyperbolicScalingMatrix (q : σ.QuadraticForms n) (x y : n → D) (t : Kˣ) : Matrix n n D :=
  1 + ((t : K) - 1) • σ.hyperbolicLineMatrix q x y +
    (((t⁻¹ : Kˣ) : K) - 1) • σ.hyperbolicLineMatrix q y x

@[simp] theorem vecMul_hyperbolicScalingMatrix (q : σ.QuadraticForms n)
    (x y z : n → D) (t : Kˣ) :
    z ᵥ* σ.hyperbolicScalingMatrix q x y t = σ.hyperbolicScaling q x y t z := by
  rw [hyperbolicScalingMatrix, Matrix.vecMul_add, Matrix.vecMul_add,
    Matrix.vecMul_one, Matrix.vecMul_smul, Matrix.vecMul_smul,
    vecMul_hyperbolicLineMatrix, vecMul_hyperbolicLineMatrix,
    hyperbolicScaling_apply, hyperbolicRemainder_apply, hyperbolicProjection_apply]
  simp only [sub_smul, one_smul]
  abel

variable {σ} {q : σ.QuadraticForms n} {x y : n → D}

namespace IsHyperbolicPair

theorem hyperbolicLineMatrix_idempotent (h : σ.IsHyperbolicPair q x y) :
    σ.hyperbolicLineMatrix q x y * σ.hyperbolicLineMatrix q x y =
      σ.hyperbolicLineMatrix q x y := by
  apply Matrix.ext_of_single_vecMul
  intro i
  rw [← Matrix.vecMul_vecMul, vecMul_hyperbolicLineMatrix,
    vecMul_hyperbolicLineMatrix,
    sesqForm_smul_left, h.2.2, mul_one]

theorem hyperbolicLineMatrix_mul_swap (h : σ.IsHyperbolicPair q x y) :
    σ.hyperbolicLineMatrix q x y * σ.hyperbolicLineMatrix q y x = 0 := by
  apply Matrix.ext_of_single_vecMul
  intro i
  rw [← Matrix.vecMul_vecMul, vecMul_hyperbolicLineMatrix,
    vecMul_hyperbolicLineMatrix, sesqForm_smul_left,
    sesqForm_polar_self_eq_zero σ q x h.1, mul_zero, zero_smul, Matrix.vecMul_zero]

/-- The explicit Laurent-scalar matrix preserves the actual quotient form. -/
theorem quadraticPullback_hyperbolicScalingMatrix (h : σ.IsHyperbolicPair q x y) (t : Kˣ) :
    σ.quadraticPullback (σ.hyperbolicScalingMatrix q x y t) q = q := by
  apply (σ.quadraticPullback_eq_iff _ _).mpr
  intro z
  rw [vecMul_hyperbolicScalingMatrix, h.quadraticValue_hyperbolicScaling]

/-- Every representative satisfies the actual matrix-defect membership condition. -/
theorem hyperbolicScalingMatrix_defect_mem (h : σ.IsHyperbolicPair q x y) (t : Kˣ)
    (Q : Matrix n n D) (hQ : (Submodule.Quotient.mk Q : σ.QuadraticForms n) = q) :
    σ.hyperbolicScalingMatrix q x y t * Q * σ.matrix n (σ.hyperbolicScalingMatrix q x y t) - Q
      ∈ σ.quadraticKernel n := by
  apply (Submodule.Quotient.eq _).mp
  rw [← σ.rectangularAdjoint_square (σ.hyperbolicScalingMatrix q x y t),
    ← quadraticPullback_mk, hQ, h.quadraticPullback_hyperbolicScalingMatrix]

end IsHyperbolicPair

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
