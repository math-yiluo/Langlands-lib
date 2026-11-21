import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Identity theorems for holomorphic and meromorphic functions of several variables

Scalar functions on a complex normed space `E` (for instance `ℂⁿ`).

* A function complex differentiable on a connected open set that vanishes near one point
  vanishes on the whole set. Mathlib proves this for analytic functions and proves analyticity
  of complex differentiable functions of one variable only; the proof restricts to complex lines.
* Scalar meromorphic functions in the sense of
  `Langlands.Analysis.Meromorphic.IsMeromorphicOn` (Bernstein–Lapid §3.1) are closed under
  finite sums and multiplication by constants, and two of them that agree on a nonempty open
  set agree wherever both are holomorphic.
* Transfer of a cleared form: if `h = p · f₂` on `W ∩ U₂`, and `f₁` agrees with `f₂` on a
  nonempty open set, then `h = p · f₁` on `W ∩ U₁`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Filter Topology Metric
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Holomorphic functions -/

/-- **Identity theorem on a convex open set.** A function complex differentiable on a convex
open set `U` that vanishes near a point of `U` vanishes on `U`. The proof restricts to the
complex line through the two points. -/
theorem eqOn_zero_of_convex_of_eventuallyEq_zero {f : E → ℂ} {U : Set E}
    (hf : DifferentiableOn ℂ f U) (hUo : IsOpen U) (hUc : Convex ℝ U) {y : E} (hy : y ∈ U)
    (h0 : f =ᶠ[𝓝 y] 0) : EqOn f 0 U := by
  intro z hz
  let L : ℂ → E := fun t => y + t • (z - y)
  have hLd : Differentiable ℂ L := by fun_prop
  let T : Set ℂ := L ⁻¹' U
  have hTo : IsOpen T := hUo.preimage hLd.continuous
  have hTc : Convex ℝ T :=
    (hUc.translate_preimage_right y).linear_preimage
      ((LinearMap.toSpanSingleton ℂ E (z - y)).restrictScalars ℝ)
  have hd : DifferentiableOn ℂ (f ∘ L) T := hf.comp hLd.differentiableOn (fun t ht => ht)
  have ha : AnalyticOnNhd ℂ (f ∘ L) T := hd.analyticOnNhd hTo
  have h0T : (0 : ℂ) ∈ T := by simpa [T, L] using hy
  have h1T : (1 : ℂ) ∈ T := by simpa [T, L] using hz
  have hev : f ∘ L =ᶠ[𝓝 0] 0 := by
    have ht : Tendsto L (𝓝 0) (𝓝 y) := by
      have := hLd.continuous.tendsto 0
      simpa [L] using this
    exact ht.eventually h0
  have := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hTc.isPreconnected h0T hev h1T
  simpa [L] using this

/-- **Identity theorem on a connected open set.** A function complex differentiable on a
preconnected open set `U` that vanishes near a point of `U` vanishes on `U`. -/
theorem eqOn_zero_of_isPreconnected_of_eventuallyEq_zero {f : E → ℂ} {U : Set E}
    (hf : DifferentiableOn ℂ f U) (hUo : IsOpen U) (hU : IsPreconnected U) {y : E}
    (hy : y ∈ U) (h0 : f =ᶠ[𝓝 y] 0) : EqOn f 0 U := by
  let Z : Set E := {x | f =ᶠ[𝓝 x] 0}
  have hZo : IsOpen Z := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ Z := by
    refine hU.subset_of_closure_inter_subset hZo ⟨y, hy, h0⟩ ?_
    rintro x ⟨hxc, hxU⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo x hxU
    obtain ⟨z, hzB, hzZ⟩ := mem_closure_iff_nhds.1 hxc (ball x ε) (ball_mem_nhds x hε)
    have hB := eqOn_zero_of_convex_of_eventuallyEq_zero (hf.mono hball) isOpen_ball
      (convex_ball x ε) hzB hzZ
    exact Filter.mem_of_superset (ball_mem_nhds x hε) (fun w hw => hB hw)
  intro x hx
  exact (hsub hx).self_of_nhds

/-- Two functions complex differentiable on a preconnected open set that agree near one of its
points agree on it. -/
theorem eqOn_of_isPreconnected_of_eventuallyEq {f g : E → ℂ} {U : Set E}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hUo : IsOpen U)
    (hU : IsPreconnected U) {y : E} (hy : y ∈ U) (hfg : f =ᶠ[𝓝 y] g) : EqOn f g U := by
  have h0 : (f - g) =ᶠ[𝓝 y] 0 := by
    filter_upwards [hfg] with x hx
    simp [hx]
  intro x hx
  have := eqOn_zero_of_isPreconnected_of_eventuallyEq_zero (hf.sub hg) hUo hU hy h0 hx
  simpa [sub_eq_zero] using this

/-- A function complex differentiable on a preconnected open set `W` and not identically zero
on `W` is not identically zero on any nonempty open subset of `W`. -/
theorem exists_ne_zero_of_isOpen_subset {g : E → ℂ} {W : Set E}
    (hg : DifferentiableOn ℂ g W) (hWo : IsOpen W) (hW : IsPreconnected W)
    (hne : ∃ s ∈ W, g s ≠ 0) {O : Set E} (hOo : IsOpen O) (hOW : O ⊆ W) (hO : O.Nonempty) :
    ∃ s ∈ O, g s ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := hO
  have h0 : g =ᶠ[𝓝 x] 0 := Filter.mem_of_superset (hOo.mem_nhds hx) (fun s hs => h s hs)
  have := eqOn_zero_of_isPreconnected_of_eventuallyEq_zero hg hWo hW (hOW hx) h0
  obtain ⟨s, hs, hgs⟩ := hne
  exact hgs (this hs)

/-- The nonvanishing set of a function complex differentiable on a preconnected open set `W`,
not identically zero on `W`, is dense in every open subset of `W`. -/
theorem subset_closure_inter_ne_zero {g : E → ℂ} {W : Set E}
    (hg : DifferentiableOn ℂ g W) (hWo : IsOpen W) (hW : IsPreconnected W)
    (hne : ∃ s ∈ W, g s ≠ 0) {O : Set E} (hOo : IsOpen O) (hOW : O ⊆ W) :
    O ⊆ closure (O ∩ {s | g s ≠ 0}) := by
  intro x hx
  rw [_root_.mem_closure_iff]
  intro o ho hxo
  obtain ⟨s, ⟨hso, hsO⟩, hgs⟩ := exists_ne_zero_of_isOpen_subset hg hWo hW hne
    (ho.inter hOo) (inter_subset_right.trans hOW) ⟨x, hxo, hx⟩
  exact ⟨s, hso, hsO, hgs⟩

/-- The product of two functions, each complex differentiable on a preconnected open set and
not identically zero there, is not identically zero on any nonempty open subset of the
intersection. -/
theorem exists_mul_ne_zero_of_isOpen_subset {g₁ g₂ : E → ℂ} {W₁ W₂ : Set E}
    (hg₁ : DifferentiableOn ℂ g₁ W₁) (hW₁o : IsOpen W₁) (hW₁ : IsPreconnected W₁)
    (hne₁ : ∃ s ∈ W₁, g₁ s ≠ 0)
    (hg₂ : DifferentiableOn ℂ g₂ W₂) (hW₂o : IsOpen W₂) (hW₂ : IsPreconnected W₂)
    (hne₂ : ∃ s ∈ W₂, g₂ s ≠ 0)
    {O : Set E} (hOo : IsOpen O) (hO₁ : O ⊆ W₁) (hO₂ : O ⊆ W₂) (hO : O.Nonempty) :
    ∃ s ∈ O, g₁ s * g₂ s ≠ 0 := by
  obtain ⟨s₁, hs₁O, hs₁⟩ := exists_ne_zero_of_isOpen_subset hg₁ hW₁o hW₁ hne₁ hOo hO₁ hO
  have hO'o : IsOpen (O ∩ g₁ ⁻¹' {0}ᶜ) :=
    (hg₁.continuousOn.mono hO₁).isOpen_inter_preimage hOo isOpen_compl_singleton
  obtain ⟨s, ⟨hsO, hs₁'⟩, hs⟩ := exists_ne_zero_of_isOpen_subset hg₂ hW₂o hW₂ hne₂ hO'o
    (inter_subset_left.trans hO₂) ⟨s₁, hs₁O, hs₁⟩
  exact ⟨s, hsO, mul_ne_zero hs₁' hs⟩

/-! ### Scalar meromorphic functions -/

/-- The definition of `IsMeromorphicOn` for scalar functions on a complex normed space, with
complex differentiability in place of the manifold notions. -/
theorem isMeromorphicOn_iff {f : E → ℂ} {U : Set E} :
    IsMeromorphicOn 𝓘(ℂ, E) f U ↔
      IsOpen U ∧ Dense U ∧ DifferentiableOn ℂ f U ∧
        ∀ s₀ : E, ∃ W : Set E, IsOpen W ∧ IsConnected W ∧ s₀ ∈ W ∧
          ∃ g h : E → ℂ, DifferentiableOn ℂ g W ∧ (∃ s ∈ W, g s ≠ 0) ∧
            DifferentiableOn ℂ h W ∧ ∀ s ∈ U ∩ W, g s * f s = h s := by
  unfold IsMeromorphicOn
  simp only [isHolomorphicOn_iff_differentiableOn_scalar, mdifferentiableOn_iff_differentiableOn,
    smul_eq_mul]

/-- The zero function is meromorphic with any open dense domain. -/
theorem isMeromorphicOn_zero_of_isOpen_dense {U : Set E} (hUo : IsOpen U) (hUd : Dense U) :
    IsMeromorphicOn 𝓘(ℂ, E) (0 : E → ℂ) U := by
  rw [isMeromorphicOn_iff]
  refine ⟨hUo, hUd, differentiableOn_const 0, fun s₀ => ?_⟩
  refine ⟨ball s₀ 1, isOpen_ball, (convex_ball s₀ 1).isConnected (nonempty_ball.2 one_pos),
    mem_ball_self one_pos, fun _ => 1, fun _ => 0, differentiableOn_const 1,
    ⟨s₀, mem_ball_self one_pos, one_ne_zero⟩, differentiableOn_const 0, ?_⟩
  intro s _
  simp

/-- A sum of two meromorphic functions with the same domain is meromorphic with that domain. -/
theorem IsMeromorphicOn.add_sameDomain {f₁ f₂ : E → ℂ} {U : Set E}
    (h₁ : IsMeromorphicOn 𝓘(ℂ, E) f₁ U) (h₂ : IsMeromorphicOn 𝓘(ℂ, E) f₂ U) :
    IsMeromorphicOn 𝓘(ℂ, E) (f₁ + f₂) U := by
  rw [isMeromorphicOn_iff] at h₁ h₂ ⊢
  obtain ⟨hUo, hUd, hd₁, hloc₁⟩ := h₁
  obtain ⟨-, -, hd₂, hloc₂⟩ := h₂
  refine ⟨hUo, hUd, hd₁.add hd₂, fun s₀ => ?_⟩
  obtain ⟨W₁, hW₁o, hW₁c, hs₁, g₁, k₁, hg₁, hne₁, hk₁, he₁⟩ := hloc₁ s₀
  obtain ⟨W₂, hW₂o, hW₂c, hs₂, g₂, k₂, hg₂, hne₂, hk₂, he₂⟩ := hloc₂ s₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hW₁o.inter hW₂o) s₀ ⟨hs₁, hs₂⟩
  have hB₁ : ball s₀ ε ⊆ W₁ := hball.trans inter_subset_left
  have hB₂ : ball s₀ ε ⊆ W₂ := hball.trans inter_subset_right
  refine ⟨ball s₀ ε, isOpen_ball, (convex_ball s₀ ε).isConnected (nonempty_ball.2 hε),
    mem_ball_self hε, fun s => g₁ s * g₂ s, fun s => g₂ s * k₁ s + g₁ s * k₂ s,
    (hg₁.mono hB₁).mul (hg₂.mono hB₂),
    exists_mul_ne_zero_of_isOpen_subset hg₁ hW₁o hW₁c.isPreconnected hne₁ hg₂ hW₂o
      hW₂c.isPreconnected hne₂ isOpen_ball hB₁ hB₂ (nonempty_ball.2 hε),
    ((hg₂.mono hB₂).mul (hk₁.mono hB₁)).add ((hg₁.mono hB₁).mul (hk₂.mono hB₂)), ?_⟩
  rintro s ⟨hsU, hsB⟩
  have e₁ := he₁ s ⟨hsU, hB₁ hsB⟩
  have e₂ := he₂ s ⟨hsU, hB₂ hsB⟩
  simp only [Pi.add_apply]
  rw [← e₁, ← e₂]
  ring

/-- A meromorphic function times a constant is meromorphic with the same domain. -/
theorem IsMeromorphicOn.mul_const {f : E → ℂ} {U : Set E}
    (hf : IsMeromorphicOn 𝓘(ℂ, E) f U) (c : ℂ) :
    IsMeromorphicOn 𝓘(ℂ, E) (fun s => f s * c) U := by
  rw [isMeromorphicOn_iff] at hf ⊢
  obtain ⟨hUo, hUd, hd, hloc⟩ := hf
  refine ⟨hUo, hUd, hd.mul_const c, fun s₀ => ?_⟩
  obtain ⟨W, hWo, hWc, hs, g, k, hg, hne, hk, he⟩ := hloc s₀
  refine ⟨W, hWo, hWc, hs, g, fun s => k s * c, hg, hne, hk.mul_const c, ?_⟩
  intro s hs'
  show g s * (f s * c) = k s * c
  rw [← he s hs']
  ring

/-- A finite sum of meromorphic functions with the same domain is meromorphic with that
domain. -/
theorem isMeromorphicOn_sum {ι : Type*} (t : Finset ι) {f : ι → E → ℂ} {U : Set E}
    (hUo : IsOpen U) (hUd : Dense U) (hf : ∀ i ∈ t, IsMeromorphicOn 𝓘(ℂ, E) (f i) U) :
    IsMeromorphicOn 𝓘(ℂ, E) (fun s => ∑ i ∈ t, f i s) U := by
  have h := Finset.sum_induction f (fun F : E → ℂ => IsMeromorphicOn 𝓘(ℂ, E) F U)
    (fun _ _ ha hb => ha.add_sameDomain hb) (isMeromorphicOn_zero_of_isOpen_dense hUo hUd) hf
  convert h using 1
  ext s
  simp [Finset.sum_apply]

/-- **Identity theorem for meromorphic functions.** Two scalar meromorphic functions on a
complex normed space that agree on a nonempty open set, wherever both are holomorphic there,
agree wherever both are holomorphic. -/
theorem IsMeromorphicOn.eq_of_eqOn_isOpen {f₁ f₂ : E → ℂ} {U₁ U₂ : Set E}
    (h₁ : IsMeromorphicOn 𝓘(ℂ, E) f₁ U₁) (h₂ : IsMeromorphicOn 𝓘(ℂ, E) f₂ U₂)
    {V : Set E} (hVo : IsOpen V) (hVne : V.Nonempty)
    (heq : ∀ s ∈ V, s ∈ U₁ → s ∈ U₂ → f₁ s = f₂ s) :
    ∀ s ∈ U₁, s ∈ U₂ → f₁ s = f₂ s := by
  rw [isMeromorphicOn_iff] at h₁ h₂
  obtain ⟨hU₁o, hU₁d, hd₁, hloc₁⟩ := h₁
  obtain ⟨hU₂o, hU₂d, hd₂, hloc₂⟩ := h₂
  have hU₁₂d : Dense (U₁ ∩ U₂) := hU₁d.inter_of_isOpen_left hU₂d hU₁o
  have hU₁₂o : IsOpen (U₁ ∩ U₂) := hU₁o.inter hU₂o
  let Z : Set E := {x | ∀ᶠ y in 𝓝 x, y ∈ U₁ → y ∈ U₂ → f₁ y = f₂ y}
  have hZo : IsOpen Z := isOpen_setOfPred_eventually_nhds
  have hsub : (univ : Set E) ⊆ Z := by
    refine (convex_univ : Convex ℝ (univ : Set E)).isPreconnected.subset_of_closure_inter_subset
      hZo ?_ ?_
    · obtain ⟨v, hv⟩ := hVne
      exact ⟨v, mem_univ v, Filter.mem_of_superset (hVo.mem_nhds hv) (fun s hs => heq s hs)⟩
    rintro x ⟨hxc, -⟩
    obtain ⟨W₁, hW₁o, hW₁c, hx₁, g₁, k₁, hg₁, hne₁, hk₁, he₁⟩ := hloc₁ x
    obtain ⟨W₂, hW₂o, hW₂c, hx₂, g₂, k₂, hg₂, hne₂, hk₂, he₂⟩ := hloc₂ x
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hW₁o.inter hW₂o) x ⟨hx₁, hx₂⟩
    set B := ball x ε with hBdef
    have hB₁ : B ⊆ W₁ := hball.trans inter_subset_left
    have hB₂ : B ⊆ W₂ := hball.trans inter_subset_right
    let H : E → ℂ := fun y => g₂ y * k₁ y - g₁ y * k₂ y
    have hHd : DifferentiableOn ℂ H B :=
      ((hg₂.mono hB₂).mul (hk₁.mono hB₁)).sub ((hg₁.mono hB₁).mul (hk₂.mono hB₂))
    have hHU : ∀ y ∈ B, y ∈ U₁ → y ∈ U₂ → H y = g₁ y * g₂ y * (f₁ y - f₂ y) := by
      intro y hyB hy₁ hy₂
      have e₁ := he₁ y ⟨hy₁, hB₁ hyB⟩
      have e₂ := he₂ y ⟨hy₂, hB₂ hyB⟩
      simp only [H]
      rw [← e₁, ← e₂]
      ring
    obtain ⟨z, hzB, hzZ⟩ := mem_closure_iff_nhds.1 hxc B (ball_mem_nhds x hε)
    -- `H` vanishes near `z`.
    have hHz : H =ᶠ[𝓝 z] 0 := by
      obtain ⟨O, hON, hOo, hzO⟩ := _root_.mem_nhds_iff.1 (Filter.inter_mem hzZ (isOpen_ball.mem_nhds hzB))
      have hOB : O ⊆ B := fun y hy => (hON hy).2
      have hEq : EqOn H 0 (O ∩ (U₁ ∩ U₂)) := by
        rintro y ⟨hyO, hy₁, hy₂⟩
        rw [hHU y (hOB hyO) hy₁ hy₂, (hON hyO).1 hy₁ hy₂, sub_self, mul_zero]
        rfl
      have hO : EqOn H 0 O :=
        hEq.of_subset_closure (hHd.continuousOn.mono hOB) continuousOn_const
          inter_subset_left (hU₁₂d.open_subset_closure_inter hOo)
      exact Filter.mem_of_superset (hOo.mem_nhds hzO) (fun y hy => hO hy)
    have hH0 : EqOn H 0 B :=
      eqOn_zero_of_convex_of_eventuallyEq_zero hHd isOpen_ball (convex_ball x ε) hzB hHz
    -- The product of the denominators is not identically zero on `B`.
    have hgd : DifferentiableOn ℂ (fun y => g₁ y * g₂ y) B := (hg₁.mono hB₁).mul (hg₂.mono hB₂)
    have hgne : ∃ s ∈ B, g₁ s * g₂ s ≠ 0 :=
      exists_mul_ne_zero_of_isOpen_subset hg₁ hW₁o hW₁c.isPreconnected hne₁ hg₂ hW₂o
        hW₂c.isPreconnected hne₂ isOpen_ball hB₁ hB₂ (nonempty_ball.2 hε)
    have hTo : IsOpen (B ∩ (U₁ ∩ U₂)) := isOpen_ball.inter hU₁₂o
    have hclos := subset_closure_inter_ne_zero hgd isOpen_ball
      (convex_ball x ε).isPreconnected hgne hTo inter_subset_left
    have hEq : EqOn f₁ f₂ ((B ∩ (U₁ ∩ U₂)) ∩ {s | g₁ s * g₂ s ≠ 0}) := by
      rintro y ⟨⟨hyB, hy₁, hy₂⟩, hy⟩
      have h0 := hH0 hyB
      rw [hHU y hyB hy₁ hy₂] at h0
      have h0' : g₁ y * g₂ y * (f₁ y - f₂ y) = 0 := h0
      rcases mul_eq_zero.1 h0' with h | h
      · exact absurd h hy
      · exact sub_eq_zero.1 h
    have hT : EqOn f₁ f₂ (B ∩ (U₁ ∩ U₂)) :=
      hEq.of_subset_closure (hd₁.continuousOn.mono fun y hy => hy.2.1)
        (hd₂.continuousOn.mono fun y hy => hy.2.2) inter_subset_left hclos
    exact Filter.mem_of_superset (ball_mem_nhds x hε) (fun y hyB hy₁ hy₂ => hT ⟨hyB, hy₁, hy₂⟩)
  intro s hs₁ hs₂
  exact (hsub (mem_univ s)).self_of_nhds hs₁ hs₂

/-- **Transfer of a cleared form.** Let `f₁` and `f₂` be scalar meromorphic functions with
domains `U₁` and `U₂` that agree on a nonempty open set. If `h` is continuous on an open set
`W` and `h = p · f₂` on `W ∩ U₂` for a continuous `p`, then `h = p · f₁` on `W ∩ U₁`. -/
theorem IsMeromorphicOn.eq_mul_of_eqOn_isOpen {f₁ f₂ : E → ℂ} {U₁ U₂ : Set E}
    (h₁ : IsMeromorphicOn 𝓘(ℂ, E) f₁ U₁) (h₂ : IsMeromorphicOn 𝓘(ℂ, E) f₂ U₂)
    {V : Set E} (hVo : IsOpen V) (hVne : V.Nonempty)
    (heq : ∀ s ∈ V, s ∈ U₁ → s ∈ U₂ → f₁ s = f₂ s)
    {W : Set E} (hWo : IsOpen W) {p h : E → ℂ} (hp : Continuous p) (hh : ContinuousOn h W)
    (hph : ∀ s ∈ W, s ∈ U₂ → h s = p s * f₂ s) :
    ∀ s ∈ W, s ∈ U₁ → h s = p s * f₁ s := by
  have hid := h₁.eq_of_eqOn_isOpen h₂ hVo hVne heq
  have hU₁ := isMeromorphicOn_iff.1 h₁
  have hU₂ := isMeromorphicOn_iff.1 h₂
  have hEq : EqOn h (fun s => p s * f₁ s) ((W ∩ U₁) ∩ U₂) := by
    rintro s ⟨⟨hsW, hs₁⟩, hs₂⟩
    show h s = p s * f₁ s
    rw [hph s hsW hs₂, hid s hs₁ hs₂]
  have hT : EqOn h (fun s => p s * f₁ s) (W ∩ U₁) :=
    hEq.of_subset_closure (hh.mono inter_subset_left)
      (hp.continuousOn.mul (hU₁.2.2.1.continuousOn.mono inter_subset_right))
      inter_subset_left (hU₂.2.1.open_subset_closure_inter (hWo.inter hU₁.1))
  intro s hsW hs₁
  exact hT ⟨hsW, hs₁⟩

end Langlands.Analysis.Meromorphic
