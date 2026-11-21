import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Scalar quadratic forms of matrices with involution -/

noncomputable section

universe u v w t

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

section MatrixForms

variable {F : Type u} {A : Type v} [CommRing F] [Ring A] [Algebra F A]
  {ι : Type w} [Fintype ι] (σ : FirstKindInvolution F A)

/-- The sesquilinear row pairing of a matrix with involution, as a bilinear map over
the central scalars. The coefficient algebra can have zero divisors. -/
def matrixSesqBilin (H : Matrix ι ι A) : (ι → A) →ₗ[F] (ι → A) →ₗ[F] A :=
  LinearMap.mk₂ F (fun x y => ∑ i, ∑ j, x i * H i j * σ (y j))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun a x y => by simp [Finset.smul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun a x y => by simp [Finset.smul_sum])

/-- Take a scalar coordinate of the value of a matrix form on a repeated argument. -/
def scalarQuadratic (ℓ : A →ₗ[F] F) (H : Matrix ι ι A) : QuadraticForm F (ι → A) :=
  ℓ.compQuadraticMap' (LinearMap.BilinMap.toQuadraticMap (σ.matrixSesqBilin H))

@[simp] theorem scalarQuadratic_apply (ℓ : A →ₗ[F] F) (H : Matrix ι ι A) (x : ι → A) :
    σ.scalarQuadratic ℓ H x = ℓ (σ.matrixSesqBilin H x x) := rfl

theorem matrixSesqBilin_apply (H : Matrix ι ι A) (x y : ι → A) :
    σ.matrixSesqBilin H x y = ∑ i, ∑ j, x i * H i j * σ (y j) := rfl

private theorem matrixSesqBilin_dotProduct (H : Matrix ι ι A) (x y : ι → A) :
    σ.matrixSesqBilin H x y = x ⬝ᵥ (H *ᵥ (σ ∘ y)) := by
  simp [matrixSesqBilin_apply, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

variable [DecidableEq ι]

/-- Gram congruence induces an isometry of the scalar quadratic forms. -/
def scalarQuadraticIsometry (ℓ : A →ₗ[F] F) {H H' : Matrix ι ι A}
    (P : (Matrix ι ι A)ˣ) (hP : P.val * H * σ.matrix ι P.val = H') :
    (σ.scalarQuadratic ℓ H').IsometryEquiv (σ.scalarQuadratic ℓ H) where
  toFun x := x ᵥ* P.val
  invFun x := x ᵥ* P.inv
  left_inv x := by
    change (x ᵥ* P.val) ᵥ* P.inv = x
    rw [vecMul_vecMul, P.val_inv, vecMul_one]
  right_inv x := by
    change (x ᵥ* P.inv) ᵥ* P.val = x
    rw [vecMul_vecMul, P.inv_val, vecMul_one]
  map_add' x y := add_vecMul _ _ _
  map_smul' a x := smul_vecMul _ _ _
  map_app' x := by
    have ha : σ ∘ (x ᵥ* P.val) = σ.matrix ι P.val *ᵥ (σ ∘ x) := by
      ext i
      simp [vecMul, mulVec, dotProduct, σ.map_sum, σ.map_mul, matrix_apply]
    rw [scalarQuadratic_apply, scalarQuadratic_apply, matrixSesqBilin_dotProduct,
      matrixSesqBilin_dotProduct, ha, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul,
      ← Matrix.mul_assoc, hP, dotProduct_mulVec]

end MatrixForms

section ScalarExtension

variable {F : Type u} {A : Type v} [CommRing F] [Ring A] [Algebra F A]
  {ι : Type w} [Fintype ι]
  (σ : FirstKindInvolution F A) (ℓ : A →ₗ[F] F) (H : Matrix ι ι A)
  (R : Type t) [CommRing R] [Algebra F R]

/-- The scalar functional extended to the coefficient algebra `R ⊗ A`. -/
def baseChangeScalarFunctional : R ⊗[F] A →ₗ[R] R :=
  (TensorProduct.AlgebraTensorModule.rid F R R).toLinearMap.comp (ℓ.baseChange R)

@[simp] theorem baseChangeScalarFunctional_tmul (r : R) (a : A) :
    baseChangeScalarFunctional ℓ R (r ⊗ₜ[F] a) = ℓ a • r := rfl

variable [Invertible (2 : F)] [DecidableEq ι]

/-- The scalar quadratic form commutes with scalar extension under the tensor row comparison. -/
theorem scalarQuadratic_baseChange :
    (σ.scalarQuadratic ℓ H).baseChange R =
      ((σ.baseChange R).scalarQuadratic (baseChangeScalarFunctional ℓ R)
        (H.map (Algebra.TensorProduct.includeRight : A →ₐ[F] R ⊗[F] A))).comp
          (TensorProduct.piRight F R R (fun _ : ι => A)).toLinearMap := by
  apply baseChange_ext
  intro x
  simp only [QuadraticForm.baseChange_tmul, scalarQuadratic_apply, QuadraticMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  have h : (σ.baseChange R).matrixSesqBilin
      (H.map (Algebra.TensorProduct.includeRight : A →ₐ[F] R ⊗[F] A))
      (fun i => 1 ⊗ₜ[F] x i) (fun i => 1 ⊗ₜ[F] x i) =
      1 ⊗ₜ[F] σ.matrixSesqBilin H x x := by
    simp only [matrixSesqBilin_apply, Matrix.map_apply, Algebra.TensorProduct.includeRight_apply,
      baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]
  rw [h, baseChangeScalarFunctional_tmul, mul_one]

end ScalarExtension

section Nondegeneracy

variable {F : Type u} {D : Type v} [Field F] [DivisionRing D] [Algebra F D]
  {ι : Type w} [Fintype ι] (σ : FirstKindInvolution F D)

@[simp] theorem matrixSesqBilin_eq_sesqForm (H : Matrix ι ι D) (x y : ι → D) :
    σ.matrixSesqBilin H x y = σ.sesqForm H x y := rfl

variable [DecidableEq ι]

theorem scalarQuadratic_polar_antihermitian (ℓ : D →ₗ[F] F) {H : Matrix ι ι D}
    (hH : σ.IsAntihermitian H) (x y : ι → D) :
    (σ.scalarQuadratic ℓ H).polarBilin x y = ℓ (σ.sesqForm H x y - σ (σ.sesqForm H x y)) := by
  rw [scalarQuadratic, LinearMap.compQuadraticMap_polarBilin,
    LinearMap.BilinMap.polarBilin_toQuadraticMap]
  simp only [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.flip_apply,
    matrixSesqBilin_eq_sesqForm, hH.sesqForm_swap σ x y, sub_eq_add_neg]

/-- The scalar form is nondegenerate if the matrix is invertible and the scalar
functional is nonzero on the alternating space. -/
theorem scalarQuadratic_nondegenerate (ℓ : D →ₗ[F] F) {H : Matrix ι ι D}
    (hH : σ.IsAntihermitian H) (hu : IsUnit H) (hℓ : ∃ a, ℓ (a - σ a) ≠ 0) :
    (σ.scalarQuadratic ℓ H).polarBilin.Nondegenerate := by
  let Q := σ.scalarQuadratic ℓ H
  have hs : Q.polarBilin.IsSymm := ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  by_contra hx0
  have hv : x ᵥ* H ≠ 0 := by
    intro hz
    apply hx0
    have heq := congrArg (fun v => v ᵥ* (↑(hu.unit⁻¹) : Matrix ι ι D)) hz
    simpa [vecMul_vecMul, hu.mul_val_inv] using heq
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  obtain ⟨a, ha⟩ := hℓ
  let y : ι → D := Pi.single j (σ (((x ᵥ* H) j)⁻¹ * a))
  have hxy : σ.sesqForm H x y = a := by
    rw [σ.sesqForm_eq_dotProduct, dotProduct_mulVec]
    have hy : σ ∘ y = Pi.single j (((x ᵥ* H) j)⁻¹ * a) := by
      ext k
      by_cases h : k = j
      · subst k
        simp [y]
      · simp [y, Pi.single_eq_of_ne h]
    rw [hy, dotProduct_single, ← mul_assoc, mul_inv_cancel₀ hj, one_mul]
  apply ha
  have h := hx y
  change (σ.scalarQuadratic ℓ H).polarBilin x y = 0 at h
  simpa only [scalarQuadratic_polar_antihermitian σ ℓ hH, hxy] using h

end Nondegeneracy

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
