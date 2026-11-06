import Langlands.Geometry.Manifold.SmoothGroupDifferential

/-! # Actual tangent conjugation and positive right-orbit differentiation -/

noncomputable section

open scoped Classical Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- The actual derivative of inner conjugation at the identity. -/
def groupTangentConjugation (g : G) : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G :=
  mfderiv I I (fun h : G => g * h * g⁻¹) 1

/-- The original positive right-orbit derivative transforms by tangent conjugation. -/
theorem groupDirectionalValue_rightTranslation
    (g : G) (X : GroupLieAlgebra I G) {f : G → ℂ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (x : G) :
    groupDirectionalValue I X f (x * g) =
      groupDirectionalValue I (groupTangentConjugation I g X) (fun y => f (y * g)) x := by
  have hconj : ContMDiff I I ∞ (fun h : G => g * h * g⁻¹) :=
    (contMDiff_const.mul contMDiff_id).mul contMDiff_const
  have horbit : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun h : G => f ((x * h) * g)) :=
    hf.comp ((contMDiff_const.mul contMDiff_id).mul contMDiff_const)
  have heq : (fun h : G => f ((x * g) * h)) =
      (fun h : G => f ((x * h) * g)) ∘ (fun h : G => g * h * g⁻¹) := by
    funext h
    simp only [Function.comp_apply]
    congr 1
    group
  change mvfderiv I (fun h => f ((x * g) * h)) 1 X =
    mvfderiv I (fun h => f ((x * h) * g)) 1 (groupTangentConjugation I g X)
  rw [heq]
  rw [mvfderiv_comp (I := I) (I' := I)
    (g := fun h : G => f ((x * h) * g))
    (f := fun h : G => g * h * g⁻¹) (1 : G)
    (horbit.mdifferentiableAt (by simp)) (hconj.mdifferentiableAt (by simp))]
  simp only [ContinuousLinearMap.comp_apply]
  exact congrArg (fun z : G =>
    (mvfderiv I (fun h : G => f ((x * h) * g)) z : E →L[ℝ] ℂ)
      (groupTangentConjugation I g X)) (by simp)

end Langlands.Geometry.Manifold
