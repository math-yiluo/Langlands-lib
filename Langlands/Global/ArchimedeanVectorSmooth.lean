import Langlands.Global.ArchimedeanGL
import Mathlib.RepresentationTheory.Intertwining

/-!
# Normed vector valued real smooth functions on actual archimedean matrix groups

The domain uses the published mixed real/complex coordinates. Coefficient maps
are continuous complex linear maps, and smoothness is over the real field.
-/

noncomputable section

universe uF uV uW uX

namespace Langlands.Global.ArchimedeanGL

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Actual vector valued functions with real smoothness in the mixed coordinates. -/
def vectorSmoothFunctions : Submodule ℂ
    (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → V) where
  carrier := {f | ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, V) ∞
    (fun x : ArchimedeanGL F n => f ((archimedeanGLCoordinates F n).symm x))}
  zero_mem' := contMDiff_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := by
    exact ((c • ContinuousLinearMap.id ℂ V).restrictScalars ℝ).contDiff.contMDiff.comp hf

/-- The genuine subspace of smooth functions, with no chosen function-space topology. -/
abbrev VectorSmoothFunctions := ↥(vectorSmoothFunctions F n V)

theorem vectorSmooth_continuous (f : VectorSmoothFunctions F n V) : Continuous f.val := by
  have h := f.property.continuous.comp (archimedeanGLCoordinates F n).continuous
  change Continuous (fun x => f.val
    ((archimedeanGLCoordinates F n).symm (archimedeanGLCoordinates F n x))) at h
  simpa only [Function.comp_def, ContinuousMulEquiv.symm_apply_apply] using h

/-- Right translation preserves real smoothness. -/
def vectorSmoothRightAction : Representation ℂ
    (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F))
    (VectorSmoothFunctions F n V) where
  toFun g :=
    { toFun f := ⟨fun x => f.val (x * g), by
        change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, V) ∞
          (fun x : ArchimedeanGL F n => f.val ((archimedeanGLCoordinates F n).symm x * g))
        have hg : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n)
            𝓘(ℝ, ArchimedeanMatrix F n) ∞
            (fun x : ArchimedeanGL F n => x * archimedeanGLCoordinates F n g) :=
          contMDiff_id.mul contMDiff_const
        simpa only [Function.comp_def, map_mul, ContinuousMulEquiv.symm_apply_apply]
          using f.property.comp hg⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext f x
    exact congrArg f.val (mul_one x)
  map_mul' g h := by
    ext f x
    exact congrArg f.val (mul_assoc x g h).symm

@[simp]
theorem vectorSmoothRightAction_apply
    (g x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F))
    (f : VectorSmoothFunctions F n V) :
    (vectorSmoothRightAction F n V g f).val x = f.val (x * g) := rfl

/-- Postcomposition by a continuous complex linear coefficient map. -/
def vectorSmoothMap (T : V →L[ℂ] W) :
    (vectorSmoothRightAction F n V).IntertwiningMap (vectorSmoothRightAction F n W) where
  toLinearMap :=
    { toFun f := ⟨fun x => T (f.val x),
        (T.restrictScalars ℝ).contDiff.contMDiff.comp f.property⟩
      map_add' f g := by ext x; exact T.map_add _ _
      map_smul' c f := by ext x; exact T.map_smul c _ }
  isIntertwining' _ := by ext f x; rfl

@[simp]
theorem vectorSmoothMap_apply (T : V →L[ℂ] W) (f : VectorSmoothFunctions F n V)
    (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (vectorSmoothMap F n V T f).val x = T (f.val x) := rfl

@[simp]
theorem vectorSmoothMap_id :
    vectorSmoothMap F n V (ContinuousLinearMap.id ℂ V) =
      Representation.IntertwiningMap.id (vectorSmoothRightAction F n V) := by
  ext f x
  rfl

@[simp]
theorem vectorSmoothMap_comp (T : V →L[ℂ] W) (S : W →L[ℂ] X) :
    vectorSmoothMap F n V (S.comp T) =
      (vectorSmoothMap F n W S).comp (vectorSmoothMap F n V T) := by
  ext f x
  rfl

/-- Faithful realization in actual continuous functions; the smooth space has no
function-space topology assigned by this construction. -/
def vectorSmoothToContinuousMap : VectorSmoothFunctions F n V →ₗ[ℂ]
    C(Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F), V) where
  toFun f := ⟨f.val, vectorSmooth_continuous F n V f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vectorSmoothToContinuousMap_injective :
    Function.Injective (vectorSmoothToContinuousMap F n V) := by
  intro f g h
  apply Subtype.ext
  exact congrArg ContinuousMap.toFun h

/-- The complex scalar case is the already published smooth function space. -/
def vectorSmoothScalarEquiv : VectorSmoothFunctions F n ℂ ≃ₗ[ℂ] SmoothFunctions F n where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem vectorSmoothScalarEquiv_rightAction
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F))
    (f : VectorSmoothFunctions F n ℂ) :
    vectorSmoothScalarEquiv F n (vectorSmoothRightAction F n ℂ g f) =
      smoothRightAction F n g (vectorSmoothScalarEquiv F n f) := rfl

end Langlands.Global.ArchimedeanGL
