import Langlands.Global.Factors.RelativeWeilEngine

/-! # Epsilon products of a global functional equation with trivial L-functions -/

noncomputable section

set_option autoImplicit false

namespace Langlands.LocalFactor.NonabelianBrauer

open Filter Topology
open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

/-- A meromorphic function on `ℂ` that is constant on a nonempty open set has the constant as
its punctured germ everywhere. -/
theorem meromorphicEq_const_of_eqOn_open {f : ℂ → ℂ} (hf : Meromorphic f) {U : Set ℂ}
    (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) (c : ℂ) (h : ∀ s ∈ U, f s = c) :
    MeromorphicEq f (fun _ => c) := by
  have hg : Meromorphic (fun s => f s - c) := fun z => (hf z).sub (MeromorphicAt.const c z)
  have htop : meromorphicOrderAt (fun s => f s - c) x = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hx)] with s hs
    rw [h s hs, sub_self]
  intro z
  have hz := (Meromorphic.meromorphicOn hg (s := Set.univ)).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ x) (Set.mem_univ z) htop
  rw [meromorphicOrderAt_eq_top_iff] at hz
  filter_upwards [hz] with s hs
  exact sub_eq_zero.mp hs

/-- Punctured germs are preserved by the reflection `s ↦ 1 - s`. -/
theorem MeromorphicEq.comp_one_sub {f g : ℂ → ℂ} (h : MeromorphicEq f g) :
    MeromorphicEq (fun s => f (1 - s)) (fun s => g (1 - s)) := by
  intro z
  have ht : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] z) (𝓝[≠] (1 - z)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.sub continuous_id).tendsto z).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h'
      exact hs (by simpa using h')
  exact (h (1 - z)).comp_tendsto ht

/-- **Epsilon products when all L-functions are trivial.** If a global functional-equation
package has all local L-factors and dual L-factors equal to `1`, and its archimedean blocks
have the punctured germs of `1`, then the product of its epsilon factors over the exceptional set
is `1` at every point where these epsilon factors are continuous. -/
theorem prod_epsilon_eq_one_of_hasGlobalEquation {Q : Type*} {l d e : Q → ℂ → ℂ}
    {A Ad Ae : ℂ → ℂ} {B : Finset Q} (h : HasGlobalEquation l d e A Ad Ae B)
    (hl : ∀ z s, l z s ≠ 0 → l z s = 1) (hd : ∀ z s, d z s ≠ 0 → d z s = 1)
    (hA : MeromorphicEq A (fun _ => 1)) (hAd : MeromorphicEq Ad (fun _ => 1))
    (hAe : MeromorphicEq Ae (fun _ => 1)) (s₀ : ℂ)
    (he : ContinuousAt (fun s => ∏ z ∈ B, e z s) s₀) :
    ∏ z ∈ B, e z s₀ = 1 := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hp, hfe⟩ := h
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hx : ((σ + 1 : ℝ) : ℂ) ∈ {s : ℂ | σ < s.re} := by simp
  have hΛ1 : MeromorphicEq Λ (fun _ => 1) := by
    refine meromorphicEq_const_of_eqOn_open hΛ hU hx 1 fun s hs => ?_
    have h1 := (hp s hs).1.1
    have h2 : HasProd (fun v => l v s) 1 := by
      have hl1 : ∀ v, l v s = 1 := fun v => hl v s (ne_zero_of_hasProd h1 (hp s hs).1.2 v)
      simp only [hl1]
      exact hasProd_one
    exact h1.unique h2
  have hΛd1 : MeromorphicEq Λd (fun _ => 1) := by
    refine meromorphicEq_const_of_eqOn_open hΛd hU hx 1 fun s hs => ?_
    have h1 := (hp s hs).2.1
    have h2 : HasProd (fun v => d v s) 1 := by
      have hd1 : ∀ v, d v s = 1 := fun v => hd v s (ne_zero_of_hasProd h1 (hp s hs).2.2 v)
      simp only [hd1]
      exact hasProd_one
    exact h1.unique h2
  have hL : MeromorphicEq (fun s => Λ s * A s) (fun _ => 1) := by
    have := MeromorphicEq.mul hΛ1 hA
    simpa using this
  have hR : MeromorphicEq (fun s => Ae s * (∏ z ∈ B, e z s) * (Λd (1 - s) * Ad (1 - s)))
      (fun s => ∏ z ∈ B, e z s) := by
    have h1 := MeromorphicEq.mul (MeromorphicEq.mul hAe (MeromorphicEq.refl
      (fun s => ∏ z ∈ B, e z s)))
      (MeromorphicEq.mul (MeromorphicEq.comp_one_sub hΛd1) (MeromorphicEq.comp_one_sub hAd))
    simpa using h1
  have hgerm : (fun s => ∏ z ∈ B, e z s) =ᶠ[𝓝[≠] s₀] (fun _ => (1 : ℂ)) :=
    ((hR s₀).symm.trans (hfe s₀).symm).trans (hL s₀)
  have hlim1 : Tendsto (fun s => ∏ z ∈ B, e z s) (𝓝[≠] s₀) (𝓝 1) :=
    tendsto_const_nhds.congr' hgerm.symm
  have hlim2 : Tendsto (fun s => ∏ z ∈ B, e z s) (𝓝[≠] s₀) (𝓝 (∏ z ∈ B, e z s₀)) :=
    he.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlim2 hlim1

end Langlands.LocalFactor.NonabelianBrauer
