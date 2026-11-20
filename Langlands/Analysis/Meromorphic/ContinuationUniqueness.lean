import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Uniqueness of meromorphic continuation in linear coordinates

The identity theorem for complex differentiable scalar functions on connected open subsets
of a complex normed space, proved by restriction to complex lines; its consequence that two
meromorphic functions (in the sense of `IsMeromorphicOn`, with local scalar denominators)
which agree near one point of a connected open set agree wherever both are holomorphic; and
the comparison of meromorphic functions on open subsets of `ℂⁿ` written in two linear
coordinate systems of one complex vector space. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Filter Topology Metric
open scoped Manifold

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The identity theorem: a complex differentiable function on a connected open set which
vanishes near one point vanishes everywhere on the set. -/
theorem eqOn_zero_of_differentiableOn_of_eventuallyEq_zero {ψ : E → ℂ} {W : Set E}
    (hW : IsOpen W) (hWc : IsPreconnected W) (hψ : DifferentiableOn ℂ ψ W) {t₀ : E}
    (ht₀ : t₀ ∈ W) (h0 : ψ =ᶠ[𝓝 t₀] 0) : ∀ y ∈ W, ψ y = 0 := by
  have hsub : W ⊆ {t | ψ =ᶠ[𝓝 t] 0} := by
    refine hWc.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨t₀, ht₀, h0⟩ ?_
    rintro t ⟨htc, htW⟩
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW t htW
    obtain ⟨t', ht'u, ht'r⟩ := Metric.mem_closure_iff.mp htc r hr
    have ht'b : t' ∈ ball t r := by rw [mem_ball, dist_comm]; exact ht'r
    have key : ∀ y ∈ ball t r, ψ y = 0 := by
      intro y hy
      let ℓ : ℂ → E := fun z => t' + z • (y - t')
      have hℓ : Differentiable ℂ ℓ :=
        (differentiable_const _).add (differentiable_id.smul_const _)
      let Z : Set ℂ := ℓ ⁻¹' ball t r
      have hZo : IsOpen Z := isOpen_ball.preimage hℓ.continuous
      have hZc : Convex ℝ Z := by
        intro z₁ hz₁ z₂ hz₂ a b ha hb hab
        have h := convex_ball t r hz₁ hz₂ ha hb hab
        have hcomb : a • ℓ z₁ + b • ℓ z₂ = (a + b) • t' + (a • z₁ + b • z₂) • (y - t') := by
          simp only [ℓ, smul_add, add_smul, smul_assoc]
          abel
        rw [hab, one_smul] at hcomb
        show ℓ (a • z₁ + b • z₂) ∈ ball t r
        rw [show ℓ (a • z₁ + b • z₂) = t' + (a • z₁ + b • z₂) • (y - t') from rfl, ← hcomb]
        exact h
      have hZ0 : (0 : ℂ) ∈ Z := by
        show t' + (0 : ℂ) • (y - t') ∈ ball t r
        simpa using ht'b
      have hZ1 : (1 : ℂ) ∈ Z := by
        show t' + (1 : ℂ) • (y - t') ∈ ball t r
        simpa using hy
      have hd : DifferentiableOn ℂ (ψ ∘ ℓ) Z :=
        (hψ.mono hrW).comp hℓ.differentiableOn (fun z hz => hz)
      have han := hd.analyticOnNhd hZo
      have hev : (ψ ∘ ℓ) =ᶠ[𝓝 0] 0 := by
        have ht : Tendsto ℓ (𝓝 0) (𝓝 t') := by
          have := hℓ.continuous.tendsto 0
          simpa [ℓ] using this
        exact ht'u.comp_tendsto ht
      have h1 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hZc.isPreconnected hZ0 hev hZ1
      simpa [ℓ] using h1
    exact Filter.eventually_of_mem (ball_mem_nhds t hr) key
  intro y hy
  exact (hsub hy).eq_of_nhds

/-- A complex differentiable function on a connected open set which does not vanish
identically does not vanish identically on any nonempty open subset. -/
theorem exists_ne_zero_of_differentiableOn {g : E → ℂ} {W : Set E} (hW : IsOpen W)
    (hWc : IsPreconnected W) (hg : DifferentiableOn ℂ g W) (hne : ∃ s ∈ W, g s ≠ 0)
    {O : Set E} (hO : IsOpen O) (hOW : O ⊆ W) (hOne : O.Nonempty) : ∃ w ∈ O, g w ≠ 0 := by
  by_contra! h
  obtain ⟨s, hsW, hs⟩ := hne
  obtain ⟨t₀, ht₀⟩ := hOne
  exact hs (eqOn_zero_of_differentiableOn_of_eventuallyEq_zero hW hWc hg (hOW ht₀)
    (Filter.eventually_of_mem (hO.mem_nhds ht₀) h) s hsW)

/-- Local scalar denominators for a scalar function `Φ`, holomorphic on `D`, at the points
of `Ω`: every point of `Ω` has a connected open neighborhood `W` with functions `g`, `h`
complex differentiable on `W`, `g` not identically zero on `W`, and `g Φ = h` on `D ∩ W`. -/
def HasLocalDenominators (Φ : E → ℂ) (D Ω : Set E) : Prop :=
  ∀ t ∈ Ω, ∃ W : Set E, IsOpen W ∧ IsPreconnected W ∧ t ∈ W ∧ ∃ g h : E → ℂ,
    DifferentiableOn ℂ g W ∧ (∃ s ∈ W, g s ≠ 0) ∧ DifferentiableOn ℂ h W ∧
      ∀ s ∈ D ∩ W, g s * Φ s = h s

theorem HasLocalDenominators.mono {Φ : E → ℂ} {D Ω Ω' : Set E}
    (h : HasLocalDenominators Φ D Ω) (hΩ : Ω' ⊆ Ω) : HasLocalDenominators Φ D Ω' :=
  fun t ht => h t (hΩ ht)

/-- Pulling local denominators back along a continuous linear equivalence. -/
theorem HasLocalDenominators.comp {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    {Φ : E → ℂ} {D Ω : Set E} (h : HasLocalDenominators Φ D Ω) (T : E₁ ≃L[ℂ] E) :
    HasLocalDenominators (Φ ∘ T) (T ⁻¹' D) (T ⁻¹' Ω) := by
  intro t ht
  obtain ⟨W, hWo, hWc, htW, g, k, hg, ⟨s, hsW, hgs⟩, hk, heq⟩ := h (T t) ht
  refine ⟨T ⁻¹' W, hWo.preimage T.continuous, ?_, htW, g ∘ T, k ∘ T,
    hg.comp T.differentiableOn (mapsTo_preimage _ _), ⟨T.symm s, by simpa using hsW, by simpa⟩,
    hk.comp T.differentiableOn (mapsTo_preimage _ _), fun x hx => heq (T x) hx⟩
  rw [← T.image_symm_eq_preimage]
  exact hWc.image _ T.symm.continuous.continuousOn

omit [NormedSpace ℂ E] in
/-- Two open sets dense in `Ω` meet every open set meeting `Ω`. -/
theorem nonempty_inter_inter_of_subset_closure {Ω D₁ D₂ O : Set E} (hΩ : IsOpen Ω)
    (hD₁ : IsOpen D₁) (hcl₁ : Ω ⊆ closure D₁) (hcl₂ : Ω ⊆ closure D₂) (hO : IsOpen O)
    {y : E} (hyO : y ∈ O) (hyΩ : y ∈ Ω) : (O ∩ D₁ ∩ D₂).Nonempty := by
  obtain ⟨z, ⟨hzO, hzΩ⟩, hzD₁⟩ :=
    _root_.mem_closure_iff.mp (hcl₁ hyΩ) (O ∩ Ω) (hO.inter hΩ) ⟨hyO, hyΩ⟩
  obtain ⟨w, ⟨⟨hwO, -⟩, hwD₁⟩, hwD₂⟩ := _root_.mem_closure_iff.mp (hcl₂ hzΩ) (O ∩ Ω ∩ D₁)
    ((hO.inter hΩ).inter hD₁) ⟨⟨hzO, hzΩ⟩, hzD₁⟩
  exact ⟨w, ⟨hwO, hwD₁⟩, hwD₂⟩

/-- Uniqueness of meromorphic continuation in a normed space: two scalar functions,
holomorphic on open sets `D₁`, `D₂` dense in a connected open set `Ω` and with local scalar
denominators at every point of `Ω`, which agree on `D₁ ∩ D₂` near one point of `Ω`, agree on
all of `Ω ∩ D₁ ∩ D₂`. -/
theorem eq_of_hasLocalDenominators {Ω D₁ D₂ : Set E} {Φ₁ Φ₂ : E → ℂ}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hcl₁ : Ω ⊆ closure D₁) (hcl₂ : Ω ⊆ closure D₂)
    (hΦ₁ : ContinuousOn Φ₁ D₁) (hΦ₂ : ContinuousOn Φ₂ D₂)
    (hloc₁ : HasLocalDenominators Φ₁ D₁ Ω) (hloc₂ : HasLocalDenominators Φ₂ D₂ Ω)
    {t₀ : E} (ht₀ : t₀ ∈ Ω) (h0 : ∀ᶠ s in 𝓝 t₀, s ∈ D₁ → s ∈ D₂ → Φ₁ s = Φ₂ s) :
    ∀ s ∈ Ω, s ∈ D₁ → s ∈ D₂ → Φ₁ s = Φ₂ s := by
  have hsub : Ω ⊆ {t | ∀ᶠ s in 𝓝 t, s ∈ D₁ → s ∈ D₂ → Φ₁ s = Φ₂ s} := by
    refine hΩc.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨t₀, ht₀, h0⟩ ?_
    rintro t ⟨htc, htΩ⟩
    obtain ⟨W₁, hW₁o, hW₁c, htW₁, g₁, h₁, hg₁, hg₁ne, hh₁, heq₁⟩ := hloc₁ t htΩ
    obtain ⟨W₂, hW₂o, hW₂c, htW₂, g₂, h₂, hg₂, hg₂ne, hh₂, heq₂⟩ := hloc₂ t htΩ
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp ((hW₁o.inter hW₂o).inter hΩ) t
      ⟨⟨htW₁, htW₂⟩, htΩ⟩
    have hB₁ : ball t r ⊆ W₁ := fun x hx => (hrW hx).1.1
    have hB₂ : ball t r ⊆ W₂ := fun x hx => (hrW hx).1.2
    have hBΩ : ball t r ⊆ Ω := fun x hx => (hrW hx).2
    obtain ⟨t', ht'u, ht'r⟩ := Metric.mem_closure_iff.mp htc r hr
    have ht'b : t' ∈ ball t r := by rw [mem_ball, dist_comm]; exact ht'r
    let ψ : E → ℂ := fun s => g₂ s * h₁ s - g₁ s * h₂ s
    have hψ : DifferentiableOn ℂ ψ (ball t r) :=
      ((hg₂.mono hB₂).mul (hh₁.mono hB₁)).sub ((hg₁.mono hB₁).mul (hh₂.mono hB₂))
    have hψD : ∀ s ∈ ball t r, s ∈ D₁ → s ∈ D₂ → ψ s = g₁ s * g₂ s * (Φ₁ s - Φ₂ s) := by
      intro s hs hs₁ hs₂
      simp only [ψ]
      rw [← heq₁ s ⟨hs₁, hB₁ hs⟩, ← heq₂ s ⟨hs₂, hB₂ hs⟩]
      ring
    obtain ⟨O, hOp, hOo, ht'O⟩ := _root_.eventually_nhds_iff.mp ht'u
    have hψ0 : ∀ y ∈ O ∩ ball t r, ψ y = 0 := by
      intro y hy
      by_contra hne
      have hcont : ContinuousAt ψ y :=
        (hψ.differentiableAt (isOpen_ball.mem_nhds hy.2)).continuousAt
      obtain ⟨O', hO'p, hO'o, hyO'⟩ := _root_.eventually_nhds_iff.mp (hcont.eventually_ne hne)
      obtain ⟨w, ⟨⟨hwO', hwO, hwB⟩, hwD₁⟩, hwD₂⟩ :=
        nonempty_inter_inter_of_subset_closure hΩ hD₁ hcl₁ hcl₂
          (hO'o.inter (hOo.inter isOpen_ball)) ⟨hyO', hy⟩ (hBΩ hy.2)
      apply hO'p w hwO'
      rw [hψD w hwB hwD₁ hwD₂, hOp w hwO hwD₁ hwD₂, sub_self, mul_zero]
    have hψall : ∀ y ∈ ball t r, ψ y = 0 :=
      eqOn_zero_of_differentiableOn_of_eventuallyEq_zero isOpen_ball
        (convex_ball t r).isPreconnected hψ ht'b
        (Filter.eventually_of_mem ((hOo.inter isOpen_ball).mem_nhds ⟨ht'O, ht'b⟩) hψ0)
    refine Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) ?_
    intro y hy hy₁ hy₂
    by_contra hne
    have hcont : ContinuousAt (fun s => Φ₁ s - Φ₂ s) y :=
      (hΦ₁.continuousAt (hD₁.mem_nhds hy₁)).sub (hΦ₂.continuousAt (hD₂.mem_nhds hy₂))
    obtain ⟨O', hO'p, hO'o, hyO'⟩ :=
      _root_.eventually_nhds_iff.mp (hcont.eventually_ne (sub_ne_zero.mpr hne))
    have hO''o : IsOpen (O' ∩ ball t r ∩ D₁ ∩ D₂) :=
      ((hO'o.inter isOpen_ball).inter hD₁).inter hD₂
    obtain ⟨w₁, hw₁O, hg₁w₁⟩ := exists_ne_zero_of_differentiableOn hW₁o hW₁c hg₁ hg₁ne hO''o
      (fun x hx => hB₁ hx.1.1.2) ⟨y, ⟨⟨hyO', hy⟩, hy₁⟩, hy₂⟩
    have hg₁c : ContinuousAt g₁ w₁ :=
      (hg₁.differentiableAt (hW₁o.mem_nhds (hB₁ hw₁O.1.1.2))).continuousAt
    obtain ⟨O₃, hO₃p, hO₃o, hw₁O₃⟩ := _root_.eventually_nhds_iff.mp (hg₁c.eventually_ne hg₁w₁)
    obtain ⟨w, ⟨hwO₃, ⟨⟨hwO', hwB⟩, hwD₁⟩, hwD₂⟩, hg₂w⟩ :=
      exists_ne_zero_of_differentiableOn hW₂o hW₂c hg₂ hg₂ne (hO₃o.inter hO''o)
        (fun x hx => hB₂ hx.2.1.1.2) ⟨w₁, hw₁O₃, hw₁O⟩
    have h0w := hψall w hwB
    rw [hψD w hwB hwD₁ hwD₂] at h0w
    exact mul_ne_zero (mul_ne_zero (hO₃p w hwO₃) hg₂w) (hO'p w hwO') h0w
  intro s hs hs₁ hs₂
  exact (hsub hs).self_of_nhds hs₁ hs₂

end Flat

section Opens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open Classical in
/-- Extension by zero of a function on an open subset. -/
def extendOpens {B : TopologicalSpace.Opens E} {β : Type*} [Zero β] (f : B → β) : E → β :=
  fun t => if h : t ∈ B then f ⟨t, h⟩ else 0

omit [NormedSpace ℂ E] in
theorem extendOpens_coe {B : TopologicalSpace.Opens E} {β : Type*} [Zero β] (f : B → β)
    (s : B) : extendOpens f (s : E) = f s := by
  simp [extendOpens, s.2]

/-- A function on an open subset of `E` which is complex differentiable for the induced
manifold structure on an open set `S` has a complex differentiable extension by zero on the
image of `S`. -/
theorem differentiableOn_extendOpens {B : TopologicalSpace.Opens E} {f : B → ℂ} {S : Set B}
    (hS : IsOpen S) (hf : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f S) :
    DifferentiableOn ℂ (extendOpens f) (Subtype.val '' S) := by
  rintro _ ⟨s, hs, rfl⟩
  have h1 : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f s := (hf s hs).mdifferentiableAt (hS.mem_nhds hs)
  have hcomp : extendOpens f ∘ Subtype.val = f := by
    funext x
    exact extendOpens_coe f x
  have h2 : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (extendOpens f ∘ Subtype.val) s := by
    rw [hcomp]; exact h1
  have h3 : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (extendOpens f) (s : E) :=
    (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val _ s).mpr h2
  exact (mdifferentiableAt_iff_differentiableAt.mp h3).differentiableWithinAt

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- A meromorphic function on an open subset `B` of `E`, composed with a continuous linear
form, gives in flat terms a scalar function holomorphic on the open dense image of its domain
of holomorphy, with local scalar denominators at every point of `B`. -/
theorem IsMeromorphicOn.flat {B : TopologicalSpace.Opens E} {v : B → V} {U : Set B}
    (hv : IsMeromorphicOn 𝓘(ℂ, E) v U) (μ : V →L[ℂ] ℂ) :
    IsOpen (Subtype.val '' U) ∧ (B : Set E) ⊆ closure (Subtype.val '' U) ∧
      DifferentiableOn ℂ (extendOpens fun s => μ (v s)) (Subtype.val '' U) ∧
      HasLocalDenominators (extendOpens fun s => μ (v s)) (Subtype.val '' U) B := by
  obtain ⟨hUo, hUd, hUh, hloc⟩ := hv
  refine ⟨B.isOpen.isOpenMap_subtype_val U hUo, fun t ht => ?_,
    differentiableOn_extendOpens hUo (hUh μ), fun t ht => ?_⟩
  · have : (⟨t, ht⟩ : B) ∈ closure U := by rw [hUd.closure_eq]; trivial
    exact image_closure_subset_closure_image continuous_subtype_val ⟨_, this, rfl⟩
  · obtain ⟨W, hWo, hWc, htW, g, h, hg, ⟨s, hsW, hgs⟩, hh, heq⟩ := hloc ⟨t, ht⟩
    refine ⟨Subtype.val '' W, B.isOpen.isOpenMap_subtype_val W hWo,
      hWc.isPreconnected.image _ continuous_subtype_val.continuousOn, ⟨_, htW, rfl⟩,
      extendOpens g, extendOpens fun s => μ (h s), differentiableOn_extendOpens hWo hg,
      ⟨s, ⟨s, hsW, rfl⟩, by rwa [extendOpens_coe]⟩, differentiableOn_extendOpens hWo (hh μ), ?_⟩
    rintro _ ⟨⟨a, haU, rfl⟩, ⟨b, hbW, hba⟩⟩
    obtain rfl := Subtype.val_injective hba
    rw [extendOpens_coe, extendOpens_coe, extendOpens_coe, ← heq b ⟨haU, hbW⟩, map_smul,
      smul_eq_mul]

end Opens

section Coordinates

/-- Uniqueness of meromorphic continuation across linear coordinate systems: let `e₁`, `e₂`
be linear coordinate systems of a complex vector space `X`, `A ⊆ X` a nonempty set open in
the first coordinates, and `v₁`, `v₂` meromorphic functions on convex open sets `B₁`, `B₂`
of coordinates containing the coordinates of `A`. If, after a continuous linear form, both
agree with one function `ψ` of the parameter at the points of `A` where they are holomorphic,
then they agree at every parameter where both are holomorphic. -/
theorem IsMeromorphicOn.eq_of_linearCoordinates {X : Type*} [AddCommGroup X] [Module ℂ X]
    {n₁ n₂ : ℕ} (e₁ : (Fin n₁ → ℂ) ≃ₗ[ℂ] X) (e₂ : (Fin n₂ → ℂ) ≃ₗ[ℂ] X) {A : Set X}
    (hA : IsOpen (e₁ ⁻¹' A)) (hAne : A.Nonempty)
    {B₁ : TopologicalSpace.Opens (Fin n₁ → ℂ)} {B₂ : TopologicalSpace.Opens (Fin n₂ → ℂ)}
    (hB₁ : Convex ℝ (B₁ : Set (Fin n₁ → ℂ))) (hB₂ : Convex ℝ (B₂ : Set (Fin n₂ → ℂ)))
    (hAB₁ : e₁ ⁻¹' A ⊆ B₁) (hAB₂ : e₂ ⁻¹' A ⊆ B₂)
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    {v₁ : B₁ → V₁} {v₂ : B₂ → V₂} {U₁ : Set B₁} {U₂ : Set B₂}
    (hv₁ : IsMeromorphicOn 𝓘(ℂ, Fin n₁ → ℂ) v₁ U₁)
    (hv₂ : IsMeromorphicOn 𝓘(ℂ, Fin n₂ → ℂ) v₂ U₂)
    (μ₁ : V₁ →L[ℂ] ℂ) (μ₂ : V₂ →L[ℂ] ℂ) (ψ : X → ℂ)
    (h₁ : ∀ s ∈ U₁, e₁ s ∈ A → μ₁ (v₁ s) = ψ (e₁ s))
    (h₂ : ∀ s ∈ U₂, e₂ s ∈ A → μ₂ (v₂ s) = ψ (e₂ s))
    {s₁ : B₁} (hs₁ : s₁ ∈ U₁) {s₂ : B₂} (hs₂ : s₂ ∈ U₂) (h : e₁ s₁ = e₂ s₂) :
    μ₁ (v₁ s₁) = μ₂ (v₂ s₂) := by
  let T : (Fin n₁ → ℂ) ≃L[ℂ] (Fin n₂ → ℂ) := (e₁.trans e₂.symm).toContinuousLinearEquiv
  have hT : ∀ t, e₂ (T t) = e₁ t := fun t => by simp [T]
  obtain ⟨hD₁o, hcl₁, hΦ₁, hloc₁⟩ := hv₁.flat μ₁
  obtain ⟨hD₂o, hcl₂, hΦ₂, hloc₂⟩ := hv₂.flat μ₂
  have hconv₂ : Convex ℝ (T ⁻¹' (B₂ : Set (Fin n₂ → ℂ))) :=
    hB₂.linear_preimage ((T : (Fin n₁ → ℂ) →L[ℂ] (Fin n₂ → ℂ)).toLinearMap.restrictScalars ℝ)
  have hΩo : IsOpen ((B₁ : Set (Fin n₁ → ℂ)) ∩ T ⁻¹' B₂) :=
    B₁.isOpen.inter (B₂.isOpen.preimage T.continuous)
  have hAΩ : ∀ t ∈ e₁ ⁻¹' A, t ∈ (B₁ : Set (Fin n₁ → ℂ)) ∩ T ⁻¹' B₂ := by
    intro t ht
    refine ⟨hAB₁ ht, hAB₂ ?_⟩
    show e₂ (T t) ∈ A
    rw [hT]; exact ht
  obtain ⟨lam, hlam⟩ := hAne
  have ht₀ : e₁.symm lam ∈ e₁ ⁻¹' A := by simpa using hlam
  have key := eq_of_hasLocalDenominators (Ω := (B₁ : Set (Fin n₁ → ℂ)) ∩ T ⁻¹' B₂)
    (D₁ := Subtype.val '' U₁) (D₂ := T ⁻¹' (Subtype.val '' U₂))
    (Φ₁ := extendOpens fun s => μ₁ (v₁ s)) (Φ₂ := (extendOpens fun s => μ₂ (v₂ s)) ∘ T) hΩo
    (hB₁.inter hconv₂).isPreconnected hD₁o (hD₂o.preimage T.continuous)
    (fun t ht => hcl₁ ht.1)
    (fun t ht => T.toHomeomorph.isOpenMap.preimage_closure_subset_closure_preimage (hcl₂ ht.2))
    hΦ₁.continuousOn (hΦ₂.continuousOn.comp T.continuous.continuousOn (mapsTo_preimage _ _))
    (hloc₁.mono fun t ht => ht.1) ((hloc₂.comp T).mono fun t ht => ht.2) (hAΩ _ ht₀)
    (Filter.eventually_of_mem (hA.mem_nhds ht₀) ?_)
  · have hTs : T s₁ = s₂ := e₂.injective (by rw [hT, h])
    have hs₁Ω : (s₁ : Fin n₁ → ℂ) ∈ (B₁ : Set (Fin n₁ → ℂ)) ∩ T ⁻¹' B₂ :=
      ⟨s₁.2, by rw [Set.mem_preimage, hTs]; exact s₂.2⟩
    have := key s₁ hs₁Ω ⟨s₁, hs₁, rfl⟩ (by rw [Set.mem_preimage, hTs]; exact ⟨s₂, hs₂, rfl⟩)
    rw [Function.comp_apply, hTs, extendOpens_coe, extendOpens_coe] at this
    exact this
  · intro t ht htD₁ htD₂
    obtain ⟨a, haU, rfl⟩ := htD₁
    obtain ⟨b, hbU, hb⟩ := htD₂
    have hbA : e₂ b ∈ A := by rw [hb, hT]; exact ht
    rw [Function.comp_apply, ← hb, extendOpens_coe, extendOpens_coe, h₁ a haU ht,
      h₂ b hbU hbA, hb, hT]

end Coordinates

end Langlands.Analysis.Meromorphic
