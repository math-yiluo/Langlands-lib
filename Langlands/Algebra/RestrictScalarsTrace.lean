import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Composition
import Mathlib.Analysis.RCLike.Basic

/-! # Traces under restriction of scalars

For a finite free `R`-algebra `A` and an `A`-linear endomorphism `f` of a finite free `A`-module,
the `R`-trace of `f` is the algebra trace of its `A`-trace. For a finite product of algebras the
algebra trace is the sum of the traces of the components, and for an `RCLike` field the real
trace of `z` is `Re z` or `2 Re z`. -/

noncomputable section

open Module

set_option autoImplicit false

namespace Langlands.Algebra.RestrictScalarsTrace

section Tower

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M] [IsScalarTower R A M]

/-- The `R`-trace of an `A`-linear endomorphism is the algebra trace of its `A`-trace. -/
theorem trace_restrictScalars [Module.Free R A] [Module.Finite R A] [Module.Free A M]
    [Module.Finite A M] (f : M →ₗ[A] M) :
    LinearMap.trace R M (f.restrictScalars R) = Algebra.trace R A (LinearMap.trace A M f) := by
  classical
  let bA := Module.Free.chooseBasis R A
  let bM := Module.Free.chooseBasis A M
  rw [LinearMap.trace_eq_matrix_trace R (bA.smulTower' bM), LinearMap.restrictScalars_toMatrix,
    LinearMap.trace_eq_matrix_trace A bM]
  simp only [Matrix.trace, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace bA, Matrix.trace]
  rfl

end Tower

section Pi

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {S : ι → Type*}
  [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]

/-- The algebra trace of a finite product of finite free algebras is the sum of the traces of
the components. -/
theorem algebraTrace_pi [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)]
    (x : (i : ι) → S i) :
    Algebra.trace R ((i : ι) → S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (S i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Pi.basis_apply, Pi.basis_repr]
  congr 2
  rw [Pi.mul_apply, Pi.single_eq_same]

end Pi

section RCLike

variable (K : Type*) [RCLike K]

/-- The real trace on an `RCLike` field with `I = 0` is the real part. -/
theorem algebraTrace_of_I_eq_zero (h : (RCLike.I : K) = 0) (z : K) :
    Algebra.trace ℝ K z = RCLike.re z := by
  let b : Basis (Fin 1) ℝ K := Basis.ofEquivFun
    { toFun := fun w => fun _ => RCLike.re w
      invFun := fun c => ((c 0 : ℝ) : K)
      left_inv := fun w => (RCLike.realRingEquiv h).symm_apply_apply w
      right_inv := fun c => by funext i; fin_cases i; simp
      map_add' := fun w w' => by funext; simp
      map_smul' := fun r w => by funext; simp [RCLike.smul_re] }
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_one, Matrix.diag,
    Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [Basis.ofEquivFun_repr_apply, Basis.coe_ofEquivFun]
  change RCLike.re (z * (((Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) 0 : ℝ) : K)) =
    RCLike.re z
  simp

/-- The real trace on an `RCLike` field with `I ≠ 0` is twice the real part. -/
theorem algebraTrace_of_I_ne_zero (h : (RCLike.I : K) ≠ 0) (z : K) :
    Algebra.trace ℝ K z = 2 * RCLike.re z := by
  have hI : RCLike.im (RCLike.I : K) = 1 := by
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := K) with h' | h'
    · exact absurd h' h
    · exact h'
  let b : Basis (Fin 2) ℝ K := Basis.ofEquivFun
    { toFun := fun w => ![RCLike.re w, RCLike.im w]
      invFun := fun c => ((c 0 : ℝ) : K) + ((c 1 : ℝ) : K) * RCLike.I
      left_inv := fun w => by simp [RCLike.re_add_im]
      right_inv := fun c => by
        funext i; fin_cases i <;> simp [hI]
      map_add' := fun w w' => by funext i; fin_cases i <;> simp
      map_smul' := fun r w => by
        funext i; fin_cases i <;> simp [RCLike.smul_re, RCLike.smul_im] }
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_two, Matrix.diag,
    Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp [b, Basis.ofEquivFun_repr_apply, Basis.coe_ofEquivFun, hI]
  ring

end RCLike

end Langlands.Algebra.RestrictScalarsTrace
