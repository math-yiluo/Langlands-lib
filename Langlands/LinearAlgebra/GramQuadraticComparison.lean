import Langlands.LinearAlgebra.OrthogonalCocycleComparison
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Gram congruence, quadratic isometry and tensor scalar extension -/

noncomputable section

universe u w

open Matrix
open scoped TensorProduct

namespace Langlands.LinearAlgebra.OrthogonalCocycleDescent

variable {R : Type u} [CommRing R] {n : Type w} [Fintype n] [DecidableEq n]

theorem bilinear_symm_of_matrix_symm {B : Matrix n n R} (hB : Bᵀ = B) :
    ∀ x y : n → R, Matrix.toLinearMap₂' R B x y = Matrix.toLinearMap₂' R B y x := by
  intro x y
  rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply',
    ← Matrix.dotProduct_transpose_mulVec B y x, hB]

variable [Invertible (2 : R)]

/-- The associated Gram matrix of the quadratic form of a symmetric matrix is that matrix. -/
theorem toMatrix_toQuadraticForm_of_symm {B : Matrix n n R} (hB : Bᵀ = B) :
    B.toQuadraticForm'.toMatrix' = B := by
  change LinearMap.toMatrix₂' R
    (QuadraticMap.associatedHom R (LinearMap.BilinMap.toQuadraticMap
      (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) B))) = B
  rw [QuadraticMap.associated_left_inverse R (bilinear_symm_of_matrix_symm hB)]
  exact LinearMap.toMatrix'_toLinearMap₂' B

theorem quadratic_toMatrix_injective :
    Function.Injective (QuadraticForm.toMatrix' : QuadraticForm R (n → R) → Matrix n n R) := by
  intro q₁ q₂ h
  apply (QuadraticMap.associated_rightInverse R).injective
  exact (LinearMap.toMatrix₂' R).injective h

/-- A congruence matrix induces the corresponding linear isometry of quadratic forms. -/
def gramIsometry {B₁ B₂ : Matrix n n R} (h₁ : B₁ᵀ = B₁) (h₂ : B₂ᵀ = B₂)
    (Q : GL n R) (hQ : gramTransform Q B₂ = B₁) :
    B₁.toQuadraticForm'.IsometryEquiv B₂.toQuadraticForm' := by
  let P : GL n R := ((Matrix.isUnit_transpose _).mpr Q.isUnit).unit
  have hP : (P : Matrix n n R) = (Q : Matrix n n R)ᵀ :=
    ((Matrix.isUnit_transpose _).mpr Q.isUnit).unit_spec
  let e : (n → R) ≃ₗ[R] (n → R) := (GeneralLinearGroup.toLin P).toLinearEquiv
  have he : LinearMap.toMatrix' e.toLinearMap = (Q : Matrix n n R)ᵀ := by
    change LinearMap.toMatrix' (Matrix.toLin' (P : Matrix n n R)) = _
    rw [LinearMap.toMatrix'_toLin', hP]
  refine ⟨e, fun x => ?_⟩
  have hcomp : B₂.toQuadraticForm'.comp e.toLinearMap = B₁.toQuadraticForm' := by
    apply quadratic_toMatrix_injective
    rw [QuadraticForm.toMatrix'_comp, he, toMatrix_toQuadraticForm_of_symm h₂,
      toMatrix_toQuadraticForm_of_symm h₁, transpose_transpose]
    exact hQ
  exact DFunLike.congr_fun hcomp x

/-- A linear isometry of quadratic forms gives a congruence of their symmetric Gram matrices. -/
theorem gramCongruent_of_equivalent {B₁ B₂ : Matrix n n R}
    (h₁ : B₁ᵀ = B₁) (h₂ : B₂ᵀ = B₂)
    (h : B₁.toQuadraticForm'.Equivalent B₂.toQuadraticForm') :
    GramCongruent B₁ B₂ := by
  obtain ⟨e⟩ := h
  let M := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
  have hM : IsUnit M :=
    LinearMap.isUnit_toMatrix'_iff.mpr
      ((Module.End.isUnit_iff _).mpr e.toLinearEquiv.bijective)
  let Q : GL n R := ((Matrix.isUnit_transpose M).mpr hM).unit
  have hQ : (Q : Matrix n n R) = Mᵀ := ((Matrix.isUnit_transpose M).mpr hM).unit_spec
  refine ⟨Q, ?_⟩
  have hcomp : B₂.toQuadraticForm'.comp e.toLinearEquiv.toLinearMap = B₁.toQuadraticForm' :=
    QuadraticMap.ext e.map_app
  have hm := congrArg QuadraticForm.toMatrix' hcomp
  rw [QuadraticForm.toMatrix'_comp, toMatrix_toQuadraticForm_of_symm h₂,
    toMatrix_toQuadraticForm_of_symm h₁] at hm
  simpa only [gramTransform, hQ, transpose_transpose] using hm

/-- Congruence and quadratic isometry agree for symmetric Gram matrices. -/
theorem gramCongruent_iff_equivalent {B₁ B₂ : Matrix n n R}
    (h₁ : B₁ᵀ = B₁) (h₂ : B₂ᵀ = B₂) :
    GramCongruent B₁ B₂ ↔ B₁.toQuadraticForm'.Equivalent B₂.toQuadraticForm' :=
  ⟨fun ⟨Q, hQ⟩ => ⟨gramIsometry h₁ h₂ Q hQ⟩, gramCongruent_of_equivalent h₁ h₂⟩

variable {A : Type u} [CommRing A] [Algebra R A]

/-- Tensor scalar extension of a matrix quadratic form agrees isometrically with
the quadratic form of the coefficientwise extended matrix. -/
def gramBaseChangeIsometry (B : Matrix n n R) :
    (B.toQuadraticForm'.baseChange A).IsometryEquiv
      ((B.map (algebraMap R A)).toQuadraticForm') := by
  let e := TensorProduct.piScalarRight R A A n
  refine ⟨e, fun x => ?_⟩
  have hq : ((B.map (algebraMap R A)).toQuadraticForm').comp e.toLinearMap =
      B.toQuadraticForm'.baseChange A := by
    apply baseChange_ext
    intro v
    change (B.map (algebraMap R A)).toQuadraticForm' (e (1 ⊗ₜ[R] v)) =
      B.toQuadraticForm'.baseChange A (1 ⊗ₜ[R] v)
    have he : e (1 ⊗ₜ[R] v) = fun i => algebraMap R A (v i) := by
      ext i
      simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Algebra.smul_def]
    rw [he]
    simp only [QuadraticForm.baseChange_tmul,
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply, smul_eq_mul, Algebra.smul_def, mul_one]
    simp only [map_sum, map_mul, Matrix.map_apply]
  exact DFunLike.congr_fun hq x

end Langlands.LinearAlgebra.OrthogonalCocycleDescent
