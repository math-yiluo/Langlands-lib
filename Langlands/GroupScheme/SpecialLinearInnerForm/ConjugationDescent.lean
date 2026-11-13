import Langlands.GroupScheme.SpecialLinearInnerForm.MatrixSpan
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Descending matrix conjugation through an injective coefficient map -/

noncomputable section

namespace Langlands.GroupScheme.SpecialLinearInnerForm

open Matrix

variable {ι R B : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing B] [Algebra R B]

/-- Conjugation by an invertible matrix as an algebra endomorphism. -/
def conjugationAlgHom (H : GL ι B) : Matrix ι ι B →ₐ[R] Matrix ι ι B where
  toFun X := (H : Matrix ι ι B) * X * ((H⁻¹ : GL ι B) : Matrix ι ι B)
  map_zero' := by simp
  map_one' := by simp
  map_add' X Y := by simp [mul_add, add_mul]
  map_mul' X Y := by simp [mul_assoc]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp

@[simp] theorem conjugationAlgHom_apply (H : GL ι B) (X : Matrix ι ι B) :
    conjugationAlgHom (R := R) H X =
      (H : Matrix ι ι B) * X * ((H⁻¹ : GL ι B) : Matrix ι ι B) := rfl

variable (φ : Matrix ι ι R →ₐ[R] Matrix ι ι B)
    (ψ : Matrix ι ι R →ₐ[R] Matrix ι ι B)
    (hSL : ∀ g : Matrix.SpecialLinearGroup ι R, ∃ y : Matrix ι ι R, φ y = ψ g)

include hSL

/-- A linear map taking determinant-one matrices into a given coefficient image
takes every matrix into that image. -/
theorem image_of_specialLinear (X : Matrix ι ι R) : ∃ y, φ y = ψ X := by
  let P : Submodule R (Matrix ι ι R) := φ.toLinearMap.range.comap ψ.toLinearMap
  have htop : (⊤ : Submodule R (Matrix ι ι R)) ≤ P := by
    rw [← span_specialLinear]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact hSL g
  exact htop (Submodule.mem_top : X ∈ (⊤ : Submodule R (Matrix ι ι R)))

variable (hφ : Function.Injective φ)

/-- Descend an algebra map through an injective coefficient map, once its values
on special-linear matrices lie in the coefficient image. -/
def descendMatrixAlgHom : Matrix ι ι R →ₐ[R] Matrix ι ι R where
  toFun X := (image_of_specialLinear φ ψ hSL X).choose
  map_zero' := by
    apply hφ
    rw [(image_of_specialLinear φ ψ hSL 0).choose_spec, map_zero, map_zero]
  map_one' := by
    apply hφ
    rw [(image_of_specialLinear φ ψ hSL 1).choose_spec, map_one, map_one]
  map_add' X Y := by
    apply hφ
    rw [(image_of_specialLinear φ ψ hSL (X + Y)).choose_spec, map_add, map_add,
      (image_of_specialLinear φ ψ hSL X).choose_spec,
      (image_of_specialLinear φ ψ hSL Y).choose_spec]
  map_mul' X Y := by
    apply hφ
    rw [(image_of_specialLinear φ ψ hSL (X * Y)).choose_spec, map_mul, map_mul,
      (image_of_specialLinear φ ψ hSL X).choose_spec,
      (image_of_specialLinear φ ψ hSL Y).choose_spec]
  commutes' r := by
    apply hφ
    rw [(image_of_specialLinear φ ψ hSL (algebraMap R _ r)).choose_spec,
      ψ.commutes, φ.commutes]

/-- The descended map recovers the original algebra map after coefficient change. -/
theorem map_descendMatrixAlgHom (X : Matrix ι ι R) :
    φ (descendMatrixAlgHom φ ψ hSL hφ X) = ψ X :=
  (image_of_specialLinear φ ψ hSL X).choose_spec

end Langlands.GroupScheme.SpecialLinearInnerForm
