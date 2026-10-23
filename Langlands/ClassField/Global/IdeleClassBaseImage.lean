import Langlands.ClassField.Global.Cohomology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Changing the base field to its image in the extension field -/

noncomputable section

namespace Langlands.ClassField.Global

open CategoryTheory

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/-- The same field automorphism, with the base field replaced by its image in `E`. -/
def baseImageAutEquiv :
    (E ≃ₐ[F] E) ≃* (E ≃ₐ[(⊥ : IntermediateField F E)] E) where
  toFun σ := σ.restrictScalars (⊥ : IntermediateField F E)
  invFun σ := σ.restrictScalars F
  left_inv σ := by ext x; rfl
  right_inv σ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

@[simp] theorem baseImageAutEquiv_apply (σ : E ≃ₐ[F] E) (x : E) :
    baseImageAutEquiv F E σ x = σ x := rfl

@[simp] theorem baseImageAutEquiv_symm_apply
    (σ : E ≃ₐ[(⊥ : IntermediateField F E)] E) (x : E) :
    (baseImageAutEquiv F E).symm σ x = σ x := rfl

variable [NumberField E]

/-- The arithmetic idele-class action depends on the field automorphism, not its base label. -/
theorem relativeIdeleClassAut_baseImage (σ : E ≃ₐ[F] E) :
    relativeIdeleClassAut (⊥ : IntermediateField F E) E (baseImageAutEquiv F E σ) =
      relativeIdeleClassAut F E σ := rfl

/-- The actual idele-class cohomology is unchanged on replacing the base by its image. -/
def relativeIdeleClassCohomologyBaseImageIso (n : ℕ) :
    relativeIdeleClassCohomology F E n ≅
      relativeIdeleClassCohomology (⊥ : IntermediateField F E) E n :=
  groupCohomology.mapIso (baseImageAutEquiv F E)
    (LinearEquiv.refl _ _) (fun _ => rfl) n

end Langlands.ClassField.Global
