import Langlands.GroupScheme.SpecialLinearInnerForm.MatrixSpan

/-! # Extension of matrix linear maps along a coefficient homomorphism -/

noncomputable section

namespace Langlands.GroupScheme.SpecialLinearInnerForm

open Matrix

variable {n R B C : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [CommRing B] [CommRing C]

/-- Extend a matrix linear map using the matrix-unit basis. -/
def extendMatrix (f : R →+* B) (α : Matrix n n R →ₗ[R] Matrix n n R) :
    Matrix n n B →ₗ[B] Matrix n n B where
  toFun X := ∑ a, ∑ b, X a b • (α (single a b 1)).map f
  map_add' X Y := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp [Finset.smul_sum, smul_smul]

theorem extendMatrix_apply (f : R →+* B)
    (α : Matrix n n R →ₗ[R] Matrix n n R) (X : Matrix n n B) :
    extendMatrix f α X = ∑ a, ∑ b, X a b • (α (single a b 1)).map f := rfl

/-- Extension agrees with the original linear map on matrices from the base. -/
theorem extendMatrix_map (f : R →+* B)
    (α : Matrix n n R →ₗ[R] Matrix n n R) (X : Matrix n n R) :
    extendMatrix f α (X.map f) = (α X).map f := by
  have hX : X = ∑ a, ∑ b, X a b • single a b 1 := by
    simpa only [smul_single, smul_eq_mul, mul_one] using matrix_eq_sum_single X
  conv_rhs => rw [hX]
  simp only [map_sum, map_smul, extendMatrix_apply, map_apply]
  ext a b
  simp [Matrix.sum_apply, Matrix.smul_apply, map_sum, map_mul]

/-- Coefficient extension is natural in the receiving coefficient ring. -/
theorem map_extendMatrix (f : R →+* B) (g : B →+* C)
    (α : Matrix n n R →ₗ[R] Matrix n n R) (X : Matrix n n B) :
    (extendMatrix f α X).map g = extendMatrix (g.comp f) α (X.map g) := by
  ext a b
  simp [extendMatrix_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum, map_mul]

/-- A linear map over the receiving ring is the extension if it has the required
values on all matrices from the original ring. -/
theorem extendMatrix_eq (f : R →+* B)
    (α : Matrix n n R →ₗ[R] Matrix n n R)
    (β : Matrix n n B →ₗ[B] Matrix n n B)
    (h : ∀ X : Matrix n n R, β (X.map f) = (α X).map f) :
    extendMatrix f α = β := by
  apply LinearMap.ext
  intro X
  have he (a b : n) : (α (single a b 1)).map f = β (single a b 1) := by
    simpa using (h (single a b 1)).symm
  rw [extendMatrix_apply]
  simp_rw [he, ← map_smul, ← map_sum]
  congr 1
  simpa only [smul_single, smul_eq_mul, mul_one] using (matrix_eq_sum_single X).symm

end Langlands.GroupScheme.SpecialLinearInnerForm
