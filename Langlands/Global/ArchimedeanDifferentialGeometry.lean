import Langlands.Global.ArchimedeanSmoothDifferential
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Left translation and the manifold formula for smooth differentiation -/

noncomputable section
universe u
open scoped Classical Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Pullback by left multiplication on the actual completion-coordinate group. -/
def smoothLeftTranslation
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    Module.End ℂ (SmoothFunctions K n) where
  toFun f := ⟨fun x => f.val (a * x), by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞
      (fun x : ArchimedeanGL K n => f.val (a * (archimedeanGLCoordinates K n).symm x))
    have ha : ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n)
        𝓘(ℝ, ArchimedeanMatrix K n) ∞
        (fun x : ArchimedeanGL K n => archimedeanGLCoordinates K n a * x) :=
      contMDiff_const.mul contMDiff_id
    simpa only [Function.comp_def, map_mul, ContinuousMulEquiv.symm_apply_apply]
      using f.property.comp ha⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem smoothLeftTranslation_apply
    (a x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : SmoothFunctions K n) :
    (smoothLeftTranslation K n a f).val x = f.val (a * x) := rfl

/-- The genuine differential is the manifold derivative in the units chart. -/
theorem smoothDifferential_eq_mfderiv (X : RealLieAlgebra K n)
    (f : SmoothFunctions K n)
    (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    (smoothDifferential K n X f).val x =
      NormedSpace.fromTangentSpace _ (mfderiv 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ)
        (fun h => f.val ((archimedeanGLCoordinates K n).symm h))
        (archimedeanGLCoordinates K n x)
        ((archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n X)) := by
  rw [(f.property.mdifferentiable (by simp) _).mfderiv]
  simp only [smoothDifferential_apply, ContinuousLinearMap.comp_apply]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

end Langlands.Global.ArchimedeanGL
