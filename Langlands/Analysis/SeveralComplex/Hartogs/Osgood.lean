import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Osgood's lemma

A function on a product `U × V` of open subsets of complex normed spaces that is holomorphic in
each factor separately and locally bounded is jointly holomorphic.

* `norm_sub_le_of_forall_norm_le`: a Lipschitz bound for a bounded holomorphic function on a ball,
  from the Schwarz lemma;
* `hasFDerivAt_of_forall_norm_le`: the derivative at the centre of a product of balls on which
  the function is bounded and separately holomorphic;
* `differentiableOn_prod_of_locallyBounded`: Osgood's lemma. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter Asymptotics
open scoped Topology

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

/-- A holomorphic function bounded by `B` on `ball x₀ r` satisfies
`‖h x - h x₀‖ ≤ 2 B / r * ‖x - x₀‖` on that ball (Schwarz lemma). -/
theorem norm_sub_le_of_forall_norm_le {h : E₁ → ℂ} {x₀ x : E₁} {r B : ℝ}
    (hd : DifferentiableOn ℂ h (ball x₀ r)) (hB : ∀ y ∈ ball x₀ r, ‖h y‖ ≤ B)
    (hx : x ∈ ball x₀ r) : ‖h x - h x₀‖ ≤ 2 * B / r * ‖x - x₀‖ := by
  have hr : 0 < r := pos_of_mem_ball hx
  have hmaps : MapsTo h (ball x₀ r) (closedBall (h x₀) (2 * B)) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hB y hy
    have h2 := hB x₀ (mem_ball_self hr)
    calc ‖h y - h x₀‖ ≤ ‖h y‖ + ‖h x₀‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hx
  simpa [dist_eq_norm] using this

/-- **Osgood's lemma, local form.** If `f` is bounded by `B` on `ball x₀ r × ball y₀ r` and
holomorphic in each variable separately there, then `f` has the derivative
`D₁ ∘ fst + D₂ ∘ snd` at `(x₀, y₀)`, where `D₁`, `D₂` are the partial derivatives. -/
theorem hasFDerivAt_of_forall_norm_le {f : E₁ × E₂ → ℂ} {x₀ : E₁} {y₀ : E₂} {r B : ℝ}
    (hr : 0 < r)
    (hf₁ : ∀ y ∈ ball y₀ r, DifferentiableOn ℂ (fun x => f (x, y)) (ball x₀ r))
    (hf₂ : ∀ x ∈ ball x₀ r, DifferentiableOn ℂ (fun y => f (x, y)) (ball y₀ r))
    (hB : ∀ x ∈ ball x₀ r, ∀ y ∈ ball y₀ r, ‖f (x, y)‖ ≤ B) :
    HasFDerivAt f ((fderiv ℂ (fun x => f (x, y₀)) x₀).comp (ContinuousLinearMap.fst ℂ E₁ E₂) +
      (fderiv ℂ (fun y => f (x₀, y)) y₀).comp (ContinuousLinearMap.snd ℂ E₁ E₂)) (x₀, y₀) := by
  set D₁ := fderiv ℂ (fun x => f (x, y₀)) x₀
  set D₂ := fderiv ℂ (fun y => f (x₀, y)) y₀
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hy₀ : y₀ ∈ ball y₀ r := mem_ball_self hr
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x₀ hx₀ y₀ hy₀)
  have h₁ : HasFDerivAt (fun x => f (x, y₀)) D₁ x₀ :=
    ((hf₁ y₀ hy₀) x₀ hx₀).differentiableAt (isOpen_ball.mem_nhds hx₀) |>.hasFDerivAt
  have h₂ : HasFDerivAt (fun y => f (x₀, y)) D₂ y₀ :=
    ((hf₂ x₀ hx₀) y₀ hy₀).differentiableAt (isOpen_ball.mem_nhds hy₀) |>.hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at h₁ h₂ ⊢
  have hfst : Tendsto (fun h : E₁ × E₂ => h.1) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_fst (X := E₁) (Y := E₂)).tendsto 0
  have hsnd : Tendsto (fun h : E₁ × E₂ => h.2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_snd (X := E₁) (Y := E₂)).tendsto 0
  have hT₂ : (fun h : E₁ × E₂ => f (x₀ + h.1, y₀) - f (x₀, y₀) - D₁ h.1) =o[𝓝 0]
      fun h => h :=
    (h₁.comp_tendsto hfst).trans_isBigO isBigO_fst_prod'
  have hT₃ : (fun h : E₁ × E₂ => f (x₀, y₀ + h.2) - f (x₀, y₀) - D₂ h.2) =o[𝓝 0]
      fun h => h :=
    (h₂.comp_tendsto hsnd).trans_isBigO isBigO_snd_prod'
  -- the mixed second difference is `O(‖h‖²)`
  have hT₁ : (fun h : E₁ × E₂ =>
      f (x₀ + h.1, y₀ + h.2) - f (x₀, y₀ + h.2) - (f (x₀ + h.1, y₀) - f (x₀, y₀)))
      =o[𝓝 0] fun h => h := by
    refine IsBigO.trans_isLittleO ?_ (isLittleO_norm_pow_id (n := 2) one_lt_two)
    refine IsBigO.of_bound (4 * B / r ^ 2) ?_
    filter_upwards [ball_mem_nhds (0 : E₁ × E₂) hr] with h hh
    rw [mem_ball_zero_iff] at hh
    have ha : ‖h.1‖ < r := (norm_fst_le h).trans_lt hh
    have hb : ‖h.2‖ < r := (norm_snd_le h).trans_lt hh
    have hxa : x₀ + h.1 ∈ ball x₀ r := by simpa [mem_ball, dist_eq_norm] using ha
    have hyb : y₀ + h.2 ∈ ball y₀ r := by simpa [mem_ball, dist_eq_norm] using hb
    set g : E₂ → ℂ := fun y => f (x₀ + h.1, y) - f (x₀, y) with hg
    have hgd : DifferentiableOn ℂ g (ball y₀ r) := (hf₂ _ hxa).sub (hf₂ _ hx₀)
    have hgB : ∀ y ∈ ball y₀ r, ‖g y‖ ≤ 2 * B / r * ‖h.1‖ := by
      intro y hy
      have := norm_sub_le_of_forall_norm_le (hf₁ y hy) (fun x hx => hB x hx y hy) hxa
      simpa [hg] using this
    have key := norm_sub_le_of_forall_norm_le hgd hgB hyb
    have e : f (x₀ + h.1, y₀ + h.2) - f (x₀, y₀ + h.2) - (f (x₀ + h.1, y₀) - f (x₀, y₀)) =
        g (y₀ + h.2) - g y₀ := by simp [hg]
    rw [e, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖g (y₀ + h.2) - g y₀‖ ≤ 2 * (2 * B / r * ‖h.1‖) / r * ‖y₀ + h.2 - y₀‖ := key
      _ = 4 * B / r ^ 2 * (‖h.1‖ * ‖h.2‖) := by
        rw [add_sub_cancel_left]; field_simp; ring
      _ ≤ 4 * B / r ^ 2 * (‖h‖ * ‖h‖) := by
        gcongr
        · exact norm_fst_le h
        · exact norm_snd_le h
      _ = 4 * B / r ^ 2 * ‖h‖ ^ 2 := by ring
  refine ((hT₁.add hT₂).add hT₃).congr_left fun h => ?_
  have e₁ : (x₀, y₀) + h = (x₀ + h.1, y₀ + h.2) := rfl
  have e₂ : (D₁.comp (ContinuousLinearMap.fst ℂ E₁ E₂) +
      D₂.comp (ContinuousLinearMap.snd ℂ E₁ E₂)) h = D₁ h.1 + D₂ h.2 := rfl
  rw [e₁, e₂]
  ring

/-- **Osgood's lemma.** A locally bounded function on a product of open sets of complex normed
spaces that is holomorphic in each variable separately is holomorphic. -/
theorem differentiableOn_prod_of_locallyBounded {f : E₁ × E₂ → ℂ} {U : Set E₁} {V : Set E₂}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf₁ : ∀ y ∈ V, DifferentiableOn ℂ (fun x => f (x, y)) U)
    (hf₂ : ∀ x ∈ U, DifferentiableOn ℂ (fun y => f (x, y)) V)
    (hb : ∀ p ∈ U ×ˢ V, ∃ B, ∀ᶠ q in 𝓝 p, ‖f q‖ ≤ B) :
    DifferentiableOn ℂ f (U ×ˢ V) := by
  rintro ⟨x₀, y₀⟩ hp
  obtain ⟨B, hB⟩ := hb _ hp
  have hN : {q | ‖f q‖ ≤ B} ∩ (U ×ˢ V) ∈ 𝓝 (x₀, y₀) :=
    inter_mem hB ((hU.prod hV).mem_nhds hp)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
  rw [← ball_prod_same] at hrN
  have hsub : ∀ x ∈ ball x₀ r, ∀ y ∈ ball y₀ r, ‖f (x, y)‖ ≤ B ∧ x ∈ U ∧ y ∈ V := by
    intro x hx y hy
    have := hrN (show (x, y) ∈ ball x₀ r ×ˢ ball y₀ r from ⟨hx, hy⟩)
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hd := hasFDerivAt_of_forall_norm_le hr
    (fun y hy => (hf₁ y (hsub x₀ (mem_ball_self hr) y hy).2.2).mono
      fun x hx => (hsub x hx y hy).2.1)
    (fun x hx => (hf₂ x (hsub x hx y₀ (mem_ball_self hr)).2.1).mono
      fun y hy => (hsub x hx y hy).2.2)
    (fun x hx y hy => (hsub x hx y hy).1)
  exact hd.differentiableAt.differentiableWithinAt

end Langlands.Analysis.SeveralComplex
