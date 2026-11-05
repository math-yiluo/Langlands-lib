import Langlands.Global.ArchimedeanFiniteVectorDifferential

/-! # Extension, linear coefficient maps and left translations for vector differentiation -/

noncomputable section

universe uF uI uJ

open scoped Classical Manifold ContDiff Matrix.Norms.Operator
open Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (ι : Type uI) [Fintype ι]
variable {κ : Type uJ} [Fintype κ]

/-- The actual derivative depends only on values on the open set of units. -/
theorem finiteVectorSmoothDifferential_eq_of_extension (X : RealLieAlgebra F n)
    (f : VectorSmoothFunctions F n (ι → ℂ))
    (Q : ArchimedeanMatrix F n → (ι → ℂ))
    (hQ : ∀ h : ArchimedeanGL F n,
      Q (h : ArchimedeanMatrix F n) = f.val ((archimedeanGLCoordinates F n).symm h))
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (finiteVectorSmoothDifferential F n ι X f).val g =
      fderiv ℝ Q (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n)
        ((archimedeanGLCoordinates F n g : ArchimedeanMatrix F n) *
          realLieAlgebraToMatrix F n X) := by
  have heq : finiteVectorCoordinateExtension F n ι f =ᶠ[𝓝
      (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n)] Q := by
    filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds
      (show (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n) ∈
        Set.range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n)
        from ⟨_, rfl⟩)] with A hA
    obtain ⟨h, rfl⟩ := hA
    rw [finiteVectorCoordinateExtension_apply, hQ]
  rw [finiteVectorSmoothDifferential_apply, heq.fderiv_eq]

/-- Fixed continuous complex-linear coefficient maps commute with the genuine
real differential on finite-coordinate vector valued smooth functions. -/
theorem finiteVectorSmoothDifferential_map (X : RealLieAlgebra F n)
    (T : (ι → ℂ) →L[ℂ] (κ → ℂ)) (f : VectorSmoothFunctions F n (ι → ℂ)) :
    finiteVectorSmoothDifferential F n κ X (vectorSmoothMap F n (ι → ℂ) T f) =
      vectorSmoothMap F n (ι → ℂ) T (finiteVectorSmoothDifferential F n ι X f) := by
  apply Subtype.ext
  funext g
  rw [finiteVectorSmoothDifferential_eq_of_extension F n κ X _
    (fun A => T (finiteVectorCoordinateExtension F n ι f A))
    (fun h => by rw [finiteVectorCoordinateExtension_apply]; rfl)]
  have h := (T.restrictScalars ℝ).hasFDerivAt.comp
    (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n)
    (finiteVectorCoordinateExtension_differentiableAt F n ι f
      (archimedeanGLCoordinates F n g)).hasFDerivAt
  rw [vectorSmoothMap_apply, finiteVectorSmoothDifferential_apply]
  exact congrArg (fun D : ArchimedeanMatrix F n →L[ℝ] (κ → ℂ) =>
    D ((archimedeanGLCoordinates F n g : ArchimedeanMatrix F n) *
      realLieAlgebraToMatrix F n X)) h.fderiv

/-- Actual pullback by left multiplication on finite-coordinate vector functions. -/
def finiteVectorSmoothLeftTranslation
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    Module.End ℂ (VectorSmoothFunctions F n (ι → ℂ)) :=
  (finiteVectorSmoothEquiv F n ι).symm.toLinearMap.comp
    ((LinearMap.pi (fun i => (smoothLeftTranslation F n a).comp (LinearMap.proj i))).comp
      (finiteVectorSmoothEquiv F n ι).toLinearMap)

@[simp]
theorem finiteVectorSmoothLeftTranslation_apply
    (a g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F))
    (f : VectorSmoothFunctions F n (ι → ℂ)) :
    (finiteVectorSmoothLeftTranslation F n ι a f).val g = f.val (a * g) := rfl

/-- The genuine real differential commutes with actual left pullback. -/
theorem finiteVectorSmoothDifferential_leftTranslation (X : RealLieAlgebra F n)
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F))
    (f : VectorSmoothFunctions F n (ι → ℂ)) :
    finiteVectorSmoothDifferential F n ι X (finiteVectorSmoothLeftTranslation F n ι a f) =
      finiteVectorSmoothLeftTranslation F n ι a (finiteVectorSmoothDifferential F n ι X f) := by
  apply Subtype.ext
  funext g i
  simp only [finiteVectorSmoothDifferential, finiteVectorSmoothLeftTranslation_apply,
    finiteVectorSmoothLieAction_apply, complexSmoothLieAction_complexify]
  change (smoothDifferential F n X
      (smoothLeftTranslation F n a (finiteVectorSmoothEquiv F n ι f i))).val g =
    (smoothLeftTranslation F n a
      (smoothDifferential F n X (finiteVectorSmoothEquiv F n ι f i))).val g
  exact congrArg (fun T : Module.End ℂ (SmoothFunctions F n) =>
    (T (finiteVectorSmoothEquiv F n ι f i)).val g)
      (smoothDifferential_leftTranslation F n X a)

end Langlands.Global.ArchimedeanGL
