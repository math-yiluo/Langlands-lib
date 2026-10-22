import Langlands.Global.ArchimedeanDifferentialCalculus

/-! # Proofs of the local matrix differential laws -/

noncomputable section

universe u

open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem ambientDifferentialCommutator : AmbientDifferentialCommutator K n := by
  intro f X Y g hf
  have hX : DifferentiableAt ℝ (fun h : ArchimedeanMatrix K n => h * X) g :=
    differentiableAt_id.mul_const X
  have hY : DifferentiableAt ℝ (fun h : ArchimedeanMatrix K n => h * Y) g :=
    differentiableAt_id.mul_const Y
  have hbr :
      VectorField.lieBracket ℝ (fun h : ArchimedeanMatrix K n => h * X)
        (fun h => h * Y) g = g * (X * Y - Y * X) := by
    change
      fderiv ℝ ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip Y) g (g * X) -
        fderiv ℝ ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip X) g (g * Y) =
          g * (X * Y - Y * X)
    simp [ContinuousLinearMap.fderiv, mul_sub, mul_assoc]
  have h := VectorField.fderiv_apply_lieBracket hf (by simp) hY hX
  rw [hbr] at h
  exact h

theorem ambientDifferentialLeftTranslation : AmbientDifferentialLeftTranslation K n := by
  intro f a X g hf
  have ha : DifferentiableAt ℝ (fun h : ArchimedeanMatrix K n => a * h) g :=
    differentiableAt_id.const_mul a
  rw [fderiv_fun_comp g hf ha]
  change fderiv ℝ f (a * g)
      (fderiv ℝ ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)) a) g (g * X)) = _
  simp [ContinuousLinearMap.fderiv, mul_assoc]

theorem ambientDifferentialLaws : AmbientDifferentialLaws K n :=
  ⟨ambientDifferentialCommutator K n, ambientDifferentialLeftTranslation K n⟩

end Langlands.Global.ArchimedeanGL
