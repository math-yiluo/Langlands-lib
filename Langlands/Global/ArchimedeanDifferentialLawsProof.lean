import Langlands.Global.ArchimedeanDifferentialLaws
import Langlands.Global.ArchimedeanDifferentialCalculusProof

/-! # Proof of the genuine smooth differential operator laws -/

noncomputable section
universe u
open scoped Classical Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem smoothDifferential_commutator : SmoothDifferentialCommutator K n := by
  intro X Y
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (smoothDifferential K n ⁅X, Y⁆ f).val x =
    (smoothDifferential K n X (smoothDifferential K n Y f)).val x -
      (smoothDifferential K n Y (smoothDifferential K n X f)).val x
  have hext (Z : RealLieAlgebra K n) (h : ArchimedeanGL K n) :
      fderiv ℝ (coordinateExtension K n f) (h : ArchimedeanMatrix K n)
          ((h : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n Z) =
        (smoothDifferential K n Z f).val ((archimedeanGLCoordinates K n).symm h) := by
    simp only [smoothDifferential_apply, ContinuousMulEquiv.apply_symm_apply]
  rw [smoothDifferential_eq_of_extension K n X (smoothDifferential K n Y f)
      (fun h => fderiv ℝ (coordinateExtension K n f) h (h * realLieAlgebraToMatrix K n Y))
      (hext Y),
    smoothDifferential_eq_of_extension K n Y (smoothDifferential K n X f)
      (fun h => fderiv ℝ (coordinateExtension K n f) h (h * realLieAlgebraToMatrix K n X))
      (hext X),
    smoothDifferential_apply, realLieAlgebraToMatrix_lie]
  exact ambientDifferentialCommutator K n (coordinateExtension K n f) _ _ _
    ((coordinateExtension_contDiffAt K n f _).of_le (by simp))

theorem smoothDifferential_leftTranslation : SmoothDifferentialLeftTranslation K n := by
  intro X a
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (smoothDifferential K n X (smoothLeftTranslation K n a f)).val x =
    (smoothDifferential K n X f).val (a * x)
  have hext (h : ArchimedeanGL K n) :
      coordinateExtension K n f
        ((archimedeanGLCoordinates K n a : ArchimedeanMatrix K n) *
          (h : ArchimedeanMatrix K n)) =
        (smoothLeftTranslation K n a f).val ((archimedeanGLCoordinates K n).symm h) := by
    change coordinateExtension K n f
      ((archimedeanGLCoordinates K n a * h : ArchimedeanGL K n) : ArchimedeanMatrix K n) = _
    simp only [coordinateExtension_apply, smoothLeftTranslation_apply, map_mul,
      ContinuousMulEquiv.symm_apply_apply]
  rw [smoothDifferential_eq_of_extension K n X (smoothLeftTranslation K n a f)
      (fun h => coordinateExtension K n f
        ((archimedeanGLCoordinates K n a : ArchimedeanMatrix K n) * h)) hext,
    smoothDifferential_apply]
  simpa only [map_mul, Units.val_mul] using
    ambientDifferentialLeftTranslation K n (coordinateExtension K n f)
      (archimedeanGLCoordinates K n a : ArchimedeanMatrix K n)
      (realLieAlgebraToMatrix K n X)
      (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
      (by simpa only [map_mul, Units.val_mul] using
        ((coordinateExtension_contDiffAt K n f (archimedeanGLCoordinates K n (a * x))).differentiableAt
          (by simp)))

theorem smoothDifferentialLaws : SmoothDifferentialLaws K n :=
  ⟨smoothDifferential_commutator K n, smoothDifferential_leftTranslation K n⟩

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    SmoothDifferentialLaws K n :=
  @smoothDifferentialLaws

end Langlands.Global.ArchimedeanGL
