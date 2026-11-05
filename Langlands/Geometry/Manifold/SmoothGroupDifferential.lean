import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Real tangent differentiation of complex functions on a smooth group -/

set_option autoImplicit false

noncomputable section

open scoped Classical Manifold ContDiff

namespace Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- Real differentiation of the positive right orbit at the identity. -/
def groupDirectionalValue (X : GroupLieAlgebra I G) (f : G → ℂ) (g : G) : ℂ :=
  mvfderiv I (fun h => f (g * h)) 1 X

/-- The derivative of a smooth complex function in a fixed invariant direction
is again smooth. -/
theorem contMDiff_groupDirectionalValue (X : GroupLieAlgebra I G) {f : G → ℂ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (groupDirectionalValue I X f) := by
  have hmul : ContMDiff (I.prod I) 𝓘(ℝ, ℂ) ∞
      (fun p : G × G => f (p.1 * p.2)) := hf.comp (contMDiff_mul I ∞)
  let fg : G → TangentBundle I G := fun g => Bundle.TotalSpace.mk' E g 0
  have sfg : ContMDiff I I.tangent ∞ fg := Bundle.contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ => Bundle.TotalSpace.mk' E 1 X
  have sfv : ContMDiff I I.tangent ∞ fv := contMDiff_const
  let F₁ : G → TangentBundle I G × TangentBundle I G := fun g => (fg g, fv g)
  have S₁ : ContMDiff I (I.tangent.prod I.tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : TangentBundle I G × TangentBundle I G → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  have S₃ := hmul.contMDiff_tangentMap (m := ∞) (by simp)
  have S := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℝ, ℂ)).comp
    ((S₃.comp S₂).comp S₁)
  convert S using 1
  funext g
  dsimp [Function.comp_def, F₁, F₂, fg, fv, tangentMap]
  rw [mfderiv_prod_eq_add_apply (hmul.mdifferentiableAt (by simp))]
  simp +instances [groupDirectionalValue, mvfderiv, equivTangentBundleProd]
  rfl

/-- The orbit derivative is the derivative of the function applied to the
actual left-invariant tangent vector. -/
theorem groupDirectionalValue_eq_invariant (X : GroupLieAlgebra I G) {f : G → ℂ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (g : G) :
    groupDirectionalValue I X f g =
      mvfderiv I f g (mulInvariantVectorField X g) := by
  have hL : ContMDiff I I ∞ (fun h : G => g * h) :=
    contMDiff_const.mul contMDiff_id
  simpa only [groupDirectionalValue, mulInvariantVectorField, Function.comp_def] using
    mvfderiv_comp_apply_of_eq (I := I) (I' := I) (1 : G)
      (hf.mdifferentiableAt (by simp)) (hL.mdifferentiableAt (by simp)) (mul_one g) X

omit [LieGroup I ∞ G] in
@[simp] theorem groupDirectionalValue_add_direction (X Y : GroupLieAlgebra I G)
    (f : G → ℂ) (g : G) :
    groupDirectionalValue I (X + Y) f g =
      groupDirectionalValue I X f g + groupDirectionalValue I Y f g := by
  exact map_add _ X Y

omit [LieGroup I ∞ G] in
@[simp] theorem groupDirectionalValue_smul_direction (c : ℝ) (X : GroupLieAlgebra I G)
    (f : G → ℂ) (g : G) :
    groupDirectionalValue I (c • X) f g = c • groupDirectionalValue I X f g := by
  exact map_smul _ c X

/-- Additivity holds on smooth functions, where the manifold derivative is genuine. -/
theorem groupDirectionalValue_add (X : GroupLieAlgebra I G) {f h : G → ℂ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℂ) ∞ h) (g : G) :
    groupDirectionalValue I X (f + h) g =
      groupDirectionalValue I X f g + groupDirectionalValue I X h g := by
  have hL : ContMDiff I I ∞ (fun y : G => g * y) := contMDiff_const.mul contMDiff_id
  change mvfderiv I ((fun y => f (g * y)) + (fun y => h (g * y))) 1 X = _
  exact congrArg (fun D : TangentSpace I (1 : G) →L[ℝ] ℂ => D X)
    (mvfderiv_add ((hf.comp hL).mdifferentiableAt (by simp))
      ((hh.comp hL).mdifferentiableAt (by simp)))

/-- Differentiation is complex-linear even though its tangent direction is real. -/
theorem groupDirectionalValue_const_smul (X : GroupLieAlgebra I G) (c : ℂ)
    {f : G → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (g : G) :
    groupDirectionalValue I X (c • f) g = c • groupDirectionalValue I X f g := by
  let L : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) c
  have hL : ContMDiff I I ∞ (fun y : G => g * y) := contMDiff_const.mul contMDiff_id
  change mvfderiv I (L ∘ (fun y => f (g * y))) 1 X = _
  rw [mvfderiv_comp (g := (L : ℂ → ℂ)) (f := fun y : G => f (g * y))
    1 (((L.contDiff (n := ∞)).contMDiff).mdifferentiableAt (by simp))
    ((hf.comp hL).mdifferentiableAt (by simp))]
  simp [mvfderiv, mfderiv_eq_fderiv, L, ContinuousLinearMap.fderiv, groupDirectionalValue]
  rfl

omit [LieGroup I ∞ G] in
/-- Left pullback commutes with the orbit derivative by associativity of the
original group multiplication. -/
theorem groupDirectionalValue_leftTranslation (X : GroupLieAlgebra I G)
    (a : G) (f : G → ℂ) (g : G) :
    groupDirectionalValue I X (fun x => f (a * x)) g =
      groupDirectionalValue I X f (a * g) := by
  simp only [groupDirectionalValue, mul_assoc]

end Langlands.Geometry.Manifold
