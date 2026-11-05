import Langlands.Global.ArchimedeanDifferentialGeometry
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-! # Faithfulness of the original real archimedean differential -/

noncomputable section

universe u

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- Original smooth functions obtained from real continuous linear functionals
on the actual mixed-coordinate matrix algebra. -/
def smoothRealLinearTest (l : ArchimedeanMatrix F n →L[ℝ] ℝ) :
    SmoothFunctions F n :=
  ⟨fun g => Complex.ofRealCLM (l (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n)), by
    let L : ArchimedeanMatrix F n →L[ℝ] ℂ := Complex.ofRealCLM.comp l
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞
      (fun g : ArchimedeanGL F n =>
        L (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm g) :
          ArchimedeanMatrix F n))
    simpa only [ContinuousMulEquiv.apply_symm_apply] using!
      (L.contDiff (n := ∞)).contMDiff.comp
        (Units.contMDiff_val (𝕜 := ℝ) (n := ∞))⟩

/-- Evaluation at the identity detects the actual real direction. -/
@[simp]
theorem smoothDifferential_realLinearTest_one
    (X : RealLieAlgebra F n) (l : ArchimedeanMatrix F n →L[ℝ] ℝ) :
    (smoothDifferential F n X (smoothRealLinearTest F n l)).val 1 =
      Complex.ofRealCLM (l (realLieAlgebraToMatrix F n X)) := by
  let L : ArchimedeanMatrix F n →L[ℝ] ℂ := Complex.ofRealCLM.comp l
  rw [smoothDifferential_eq_of_extension F n X (smoothRealLinearTest F n l) L]
  · simp only [ContinuousLinearMap.fderiv, map_one, Units.val_one, one_mul]
    rfl
  · intro h
    simp only [smoothRealLinearTest, ContinuousMulEquiv.apply_symm_apply]
    rfl

/-- The original real directional differential is faithful, also in rank zero. -/
theorem realSmoothDifferential_injective :
    Function.Injective (realSmoothDifferential F n) := by
  intro X Y h
  apply (realLieAlgebraToMatrix F n).injective
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro l
  have he := congrArg (fun T : Module.End ℂ (SmoothFunctions F n) =>
    (T (smoothRealLinearTest F n l)).val 1) h
  change (smoothDifferential F n X (smoothRealLinearTest F n l)).val 1 =
    (smoothDifferential F n Y (smoothRealLinearTest F n l)).val 1 at he
  simpa only [smoothDifferential_realLinearTest_one, Complex.ofRealCLM_apply,
    Complex.ofReal_inj] using he

end Langlands.Global.ArchimedeanGL
