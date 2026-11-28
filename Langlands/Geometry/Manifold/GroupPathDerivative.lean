import Langlands.Global.AdelicUnipotentConstantTermOscillation

/-! # Derivatives along paths and finite-order orbit derivatives on a Lie group -/

noncomputable section

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup 𝓘(ℝ, E) ∞ G]

local notation "IG" => 𝓘(ℝ, E)

/-- **Derivative along a path.** If `f` is differentiable at `c t` and the path `c` is
differentiable at `t`, then `s ↦ f (c s)` has derivative at `t` the orbit derivative of `f` at
`c t` in the direction of the path velocity translated to the identity. -/
theorem hasDerivAt_comp_path {f : G → ℂ} {c : ℝ → G} {t : ℝ}
    (hf : MDifferentiableAt IG 𝓘(ℝ, ℂ) f (c t)) (hc : MDifferentiableAt 𝓘(ℝ, ℝ) IG c t) :
    HasDerivAt (fun s => f (c s))
      (groupDirectionalValue IG (leftPathVelocity c t) f (c t)) t := by
  let n : ℝ → G := fun s => (c t)⁻¹ * c s
  let b : G → ℂ := fun y => f (c t * y)
  have heq : (fun s => f (c s)) = b ∘ n := by
    funext s
    simp only [Function.comp_apply, b, n, mul_inv_cancel_left]
  have hn₁ : n t = 1 := inv_mul_cancel _
  have hn : MDifferentiableAt 𝓘(ℝ, ℝ) IG n t :=
    (mdifferentiableAt_mul_left (a := (c t)⁻¹) (b := c t)).comp t hc
  have hL : MDifferentiableAt IG IG (fun y : G => c t * y) 1 := mdifferentiableAt_mul_left
  have hb : MDifferentiableAt IG 𝓘(ℝ, ℂ) b (n t) := by
    rw [hn₁]
    have hf' : MDifferentiableAt IG 𝓘(ℝ, ℂ) f (c t * 1) := by rwa [mul_one]
    exact hf'.comp (1 : G) hL
  have hbn : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (b ∘ n) t := hb.comp t hn
  have hd : DifferentiableAt ℝ (b ∘ n) t := mdifferentiableAt_iff_differentiableAt.mp hbn
  rw [heq]
  convert hd.hasDerivAt using 1
  rw [← fderiv_apply_one_eq_deriv,
    show fderiv ℝ (b ∘ n) t 1 = mvfderiv 𝓘(ℝ, ℝ) (b ∘ n) t 1 from
      (DFunLike.congr_fun (mvfderiv_eq_fderiv (f := b ∘ n) (x := t)) 1).symm,
    mvfderiv_comp t hb hn]
  symm
  change (mvfderiv IG b (n t) : E →L[ℝ] ℂ) ((mfderiv 𝓘(ℝ, ℝ) IG n t : ℝ →L[ℝ] E) 1) = _
  rw [hn₁]
  rfl

/-- The orbit derivative of a `Cⁿ` function is of class `Cᵐ` when `m + 1 ≤ n`. -/
theorem contMDiff_groupDirectionalValue_of_le {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hn : n ≤ ∞) (X : GroupLieAlgebra IG G) {f : G → ℂ} (hf : ContMDiff IG 𝓘(ℝ, ℂ) n f) :
    ContMDiff IG 𝓘(ℝ, ℂ) m (groupDirectionalValue IG X f) := by
  have hmul : ContMDiff (ModelWithCorners.prod IG IG) 𝓘(ℝ, ℂ) n
      (fun p : G × G => f (p.1 * p.2)) := hf.comp ((contMDiff_mul IG ∞).of_le hn)
  let fg : G → TangentBundle IG G := fun g => Bundle.TotalSpace.mk' E g 0
  have sfg : ContMDiff IG (ModelWithCorners.tangent IG) m fg := Bundle.contMDiff_zeroSection _ _
  let fv : G → TangentBundle IG G := fun _ => Bundle.TotalSpace.mk' E 1 X
  have sfv : ContMDiff IG (ModelWithCorners.tangent IG) m fv := contMDiff_const
  let F₁ : G → TangentBundle IG G × TangentBundle IG G := fun g => (fg g, fv g)
  have S₁ : ContMDiff IG (ModelWithCorners.prod (ModelWithCorners.tangent IG) (ModelWithCorners.tangent IG)) m F₁ := sfg.prodMk sfv
  let F₂ : TangentBundle IG G × TangentBundle IG G → TangentBundle (ModelWithCorners.prod IG IG) (G × G) :=
    (equivTangentBundleProd IG G IG G).symm
  have S₂ : ContMDiff (ModelWithCorners.prod (ModelWithCorners.tangent IG) (ModelWithCorners.tangent IG)) (ModelWithCorners.tangent (ModelWithCorners.prod IG IG)) m F₂ :=
    contMDiff_equivTangentBundleProd_symm
  have S₃ := hmul.contMDiff_tangentMap (m := m) hmn
  have S := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℝ, ℂ)).comp
    ((S₃.comp S₂).comp S₁)
  have hmulD : MDifferentiable (ModelWithCorners.prod IG IG) 𝓘(ℝ, ℂ) (fun p : G × G => f (p.1 * p.2)) :=
    hmul.mdifferentiable (by rintro rfl; simp at hmn)
  convert S using 1
  funext g
  dsimp [Function.comp_def, F₁, F₂, fg, fv, tangentMap]
  rw [mfderiv_prod_eq_add_apply (hmulD _)]
  simp +instances [groupDirectionalValue, mvfderiv, equivTangentBundleProd]
  rfl

end

end Langlands.Geometry.Manifold
