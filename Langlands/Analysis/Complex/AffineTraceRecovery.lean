import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-! # Recovery of two half-plane traces at arbitrary parameter values -/

noncomputable section

open Filter Set Metric
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

private theorem eqOn_trace_at_parameter {F Z : ℂ × ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hSn : S.Nonempty) (σ : ℝ)
    (hF : ∀ s : ℂ, Differentiable ℂ (fun z => F (z, s)))
    (hZ : ∀ R : ℝ, ∃ τ : ℝ, DifferentiableOn ℂ Z (ball (0 : ℂ) R ×ˢ {s : ℂ | τ < s.re}))
    (hEq : ∀ z ∈ S, ∀ s : ℂ, σ < s.re → F (z, s) = Z (z, s)) (u : ℂ) :
    ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → F (u, s) = Z (u, s) := by
  obtain ⟨z₀, hz₀⟩ := hSn
  let R := max ‖u‖ ‖z₀‖ + 1
  have hu : u ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr ((le_max_left _ _).trans_lt (lt_add_one _))
  have hz : z₀ ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr ((le_max_right _ _).trans_lt (lt_add_one _))
  obtain ⟨τ, hτ⟩ := hZ R
  refine ⟨max σ τ, fun s hs => ?_⟩
  let j (z : ℂ) : ℂ × ℂ := (z, s)
  have hj : Differentiable ℂ j := Differentiable.prodMk differentiable_id (differentiable_const s)
  have hZs : DifferentiableOn ℂ (fun z => Z (z, s)) (ball (0 : ℂ) R) :=
    hτ.comp hj.differentiableOn (fun _ h => ⟨h, (le_max_right σ τ).trans_lt hs⟩)
  have he : (fun z => F (z, s)) =ᶠ[𝓝 z₀] (fun z => Z (z, s)) :=
    Filter.Eventually.mono (hS.mem_nhds hz₀) fun z hz => hEq z hz s ((le_max_left σ τ).trans_lt hs)
  exact ((hF s).differentiableOn.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hZs.analyticOnNhd isOpen_ball) (convex_ball (0 : ℂ) R).isPreconnected hz he hu

/-- If a function holomorphic along complex curves agrees with the ordinary positive
and reflected negative traces on nonempty open parameter sets, these agreements
extend to every parameter on sufficiently far right half-planes whenever the
ordinary traces are jointly holomorphic there on each bounded parameter disk. -/
def AffineTraceRecoveryStatement : Prop :=
  ∀ (F Z Zd : ℂ × ℂ → ℂ) (S Sd : Set ℂ) (σ σd : ℝ),
    IsOpen S → IsOpen Sd → S.Nonempty → Sd.Nonempty →
    (∀ γ : ℂ → ℂ × ℂ, Differentiable ℂ γ → Differentiable ℂ (F ∘ γ)) →
    (∀ R : ℝ, ∃ τ : ℝ,
      DifferentiableOn ℂ Z (ball (0 : ℂ) R ×ˢ {s : ℂ | τ < s.re}) ∧
      DifferentiableOn ℂ Zd (ball (0 : ℂ) R ×ˢ {s : ℂ | τ < s.re})) →
    (∀ z ∈ S, ∀ s : ℂ, σ < s.re → F (z, s) = Z (z, s)) →
    (∀ z ∈ Sd, ∀ s : ℂ, σd < s.re → F (z, 1 - s) = Zd (z, s)) →
    ∀ u : ℂ, ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → F (u, s) = Z (u, s) ∧ F (u, 1 - s) = Zd (u, s)

theorem affineTraceRecovery : AffineTraceRecoveryStatement := by
  intro F Z Zd S Sd σ σd hS hSd hSne hSdne hF hHol hZ hZd u
  have hp (s : ℂ) : Differentiable ℂ (fun z => F (z, s)) :=
    hF (fun z => (z, s)) (Differentiable.prodMk differentiable_id (differentiable_const s))
  obtain ⟨τ, hτ⟩ := eqOn_trace_at_parameter hS hSne σ hp
    (fun R => let ⟨b, h⟩ := hHol R; ⟨b, h.1⟩) hZ u
  obtain ⟨τd, hτd⟩ := eqOn_trace_at_parameter (F := fun p => F (p.1, 1 - p.2)) hSd hSdne σd
    (fun s => hp (1 - s)) (fun R => let ⟨b, h⟩ := hHol R; ⟨b, h.2⟩) hZd u
  exact ⟨max τ τd, fun s hs =>
    ⟨hτ s ((le_max_left _ _).trans_lt hs), hτd s ((le_max_right _ _).trans_lt hs)⟩⟩

end Langlands.Analysis
