import Langlands.Global.ArchimedeanVectorSmooth
import Langlands.Global.ArchimedeanEnvelopingAction

/-! # Actual differentials on smooth finite-coordinate vector functions -/

noncomputable section

universe uF uI

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (ι : Type uI) [Fintype ι]

/-- All finite-coordinate vector valued smooth functions are exactly families
of scalar smooth functions, using the original coordinate maps. -/
def finiteVectorSmoothEquiv :
    VectorSmoothFunctions F n (ι → ℂ) ≃ₗ[ℂ] (ι → SmoothFunctions F n) where
  toFun f i := ⟨fun g => f.val g i, contMDiff_pi_space.mp f.property i⟩
  invFun f := ⟨fun g i => (f i).val g, contMDiff_pi_space.mpr (fun i => (f i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem finiteVectorSmoothEquiv_apply (f : VectorSmoothFunctions F n (ι → ℂ))
    (i : ι) (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (finiteVectorSmoothEquiv F n ι f i).val g = f.val g i := rfl

@[simp]
theorem finiteVectorSmoothEquiv_rightAction
    (h : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F))
    (f : VectorSmoothFunctions F n (ι → ℂ)) (i : ι) :
    finiteVectorSmoothEquiv F n ι (vectorSmoothRightAction F n (ι → ℂ) h f) i =
      smoothRightAction F n h (finiteVectorSmoothEquiv F n ι f i) := rfl

private def coordinatewiseEnd :
    Module.End ℂ (SmoothFunctions F n) →ₐ[ℂ] Module.End ℂ (ι → SmoothFunctions F n) where
  toFun A :=
    { toFun f i := A (f i)
      map_add' f g := by funext i; exact map_add A (f i) (g i)
      map_smul' c f := by funext i; exact map_smul A c (f i) }
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The genuine scalar differential Lie action transported through actual
finite vector coordinates. -/
def finiteVectorSmoothLieAction :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (VectorSmoothFunctions F n (ι → ℂ)) :=
  (finiteVectorSmoothEquiv F n ι).symm.lieConj.toLieHom.comp
    ((coordinatewiseEnd F n ι).toLieHom.comp (complexSmoothLieAction F n))

@[simp]
theorem finiteVectorSmoothLieAction_apply (X : ComplexLieAlgebra F n)
    (f : VectorSmoothFunctions F n (ι → ℂ))
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) (i : ι) :
    (finiteVectorSmoothLieAction F n ι X f).val g i =
      (complexSmoothLieAction F n X (finiteVectorSmoothEquiv F n ι f i)).val g := rfl

/-- Real directional differentiation on the actual vector valued smooth space. -/
def finiteVectorSmoothDifferential (X : RealLieAlgebra F n) :
    Module.End ℂ (VectorSmoothFunctions F n (ι → ℂ)) :=
  finiteVectorSmoothLieAction F n ι (complexify F n X)

/-- The original units-chart expression of the vector valued smooth function. -/
def finiteVectorCoordinateExtension (f : VectorSmoothFunctions F n (ι → ℂ)) :
    ArchimedeanMatrix F n → (ι → ℂ) :=
  fun A i => coordinateExtension F n (finiteVectorSmoothEquiv F n ι f i) A

@[simp]
theorem finiteVectorCoordinateExtension_apply (f : VectorSmoothFunctions F n (ι → ℂ))
    (g : ArchimedeanGL F n) :
    finiteVectorCoordinateExtension F n ι f (g : ArchimedeanMatrix F n) =
      f.val ((archimedeanGLCoordinates F n).symm g) := by
  funext i
  exact coordinateExtension_apply F n _ g

/-- Every coordinate is genuinely differentiable on the open units neighborhood,
so the vector valued chart expression has an actual Frechet derivative there. -/
theorem finiteVectorCoordinateExtension_differentiableAt
    (f : VectorSmoothFunctions F n (ι → ℂ)) (g : ArchimedeanGL F n) :
    DifferentiableAt ℝ (finiteVectorCoordinateExtension F n ι f)
      (g : ArchimedeanMatrix F n) :=
  differentiableAt_pi.mpr (fun i =>
    (coordinateExtension_contDiffAt F n (finiteVectorSmoothEquiv F n ι f i) g).differentiableAt
      (by simp))

/-- The transported operator is exactly real Frechet differentiation in the
original left-invariant direction g*X, with the right-translation sign convention. -/
theorem finiteVectorSmoothDifferential_apply (X : RealLieAlgebra F n)
    (f : VectorSmoothFunctions F n (ι → ℂ))
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (finiteVectorSmoothDifferential F n ι X f).val g =
      fderiv ℝ (finiteVectorCoordinateExtension F n ι f)
        (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n)
        ((archimedeanGLCoordinates F n g : ArchimedeanMatrix F n) *
          realLieAlgebraToMatrix F n X) := by
  have hd (i : ι) :=
    (coordinateExtension_contDiffAt F n (finiteVectorSmoothEquiv F n ι f i)
      (archimedeanGLCoordinates F n g)).differentiableAt (by simp)
  funext i
  rw [finiteVectorSmoothDifferential, finiteVectorSmoothLieAction_apply,
    complexSmoothLieAction_complexify, smoothDifferential_apply]
  exact (congrArg (fun T : ArchimedeanMatrix F n →L[ℝ] (ι → ℂ) =>
    T ((archimedeanGLCoordinates F n g : ArchimedeanMatrix F n) *
      realLieAlgebraToMatrix F n X) i) (fderiv_pi hd)).symm

end Langlands.Global.ArchimedeanGL
