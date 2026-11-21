import Langlands.Analysis.SeveralComplex.CompactParameterEntireContinuation
import Langlands.Analysis.LandauDirichlet

/-! # Continuation of an entire reflection identity in a parameter -/

noncomputable section

open Metric Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SeveralComplex

/-- Entire witnesses for two right half-plane functions related by spectral reflection. -/
def HasEntireSpectralReflection (F G E : ℂ → ℂ) : Prop :=
  ∃ N Nd : ℂ → ℂ, Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → N s = F s ∧ Nd s = G s) ∧
    ∀ s : ℂ, Nd (1 - s) = E s * N s

/-- An entire reflection identity near parameter `0` propagates to parameter `1`
for two jointly holomorphic functions on uniform right half-planes. -/
def EntireSpectralReflectionStatement : Prop :=
  ∀ (F G E : ℂ × ℂ → ℂ) (σ : ℝ),
    DifferentiableOn ℂ F (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
    DifferentiableOn ℂ G (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
    Differentiable ℂ E → (∀ p, E p ≠ 0) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
      HasEntireSpectralReflection (fun s => F (z, s)) (fun s => G (z, s)) (fun s => E (z, s))) →
    HasEntireSpectralReflection (fun s => F (1, s)) (fun s => G (1, s)) (fun s => E (1, s))

theorem entireSpectralReflection : EntireSpectralReflectionStatement := by
  intro F G E σ hF hG hE hE₀ ⟨δ, hδ, hInit⟩
  let P : Set ℂ := ball 0 3
  let R : Set ℂ := {s : ℂ | σ < s.re}
  let L : Set ℂ := {s : ℂ | s.re < 1 - σ}
  let ρ (s : ℂ) := 1 - s
  have hρd : Differentiable ℂ ρ := differentiable_id.const_sub 1
  have hρρ (s : ℂ) : ρ (ρ s) = s := sub_sub_cancel 1 s
  have hρ (s : ℂ) : ρ s ∈ R ↔ s ∈ L := by
    change (σ < (1 - s).re) ↔ s.re < 1 - σ
    rw [Complex.sub_re, Complex.one_re]
    exact lt_sub_comm
  let H (p : ℂ × ℂ) := G (p.1, ρ p.2) / E p
  have hH : DifferentiableOn ℂ H (P ×ˢ L) := by
    have hcomp : Differentiable ℂ (fun p : ℂ × ℂ => (p.1, ρ p.2)) :=
      differentiable_fst.prodMk (hρd.comp differentiable_snd)
    have hm : MapsTo (fun p : ℂ × ℂ => (p.1, ρ p.2)) (P ×ˢ L) (P ×ˢ R) :=
      fun p hp => ⟨hp.1, (hρ p.2).2 hp.2⟩
    have hg : DifferentiableOn ℂ (fun p : ℂ × ℂ => G (p.1, ρ p.2)) (P ×ˢ L) :=
      DifferentiableOn.comp hG hcomp.differentiableOn hm
    change DifferentiableOn ℂ
      ((fun p : ℂ × ℂ => G (p.1, ρ p.2)) * E⁻¹) (P ×ˢ L)
    exact hg.mul (hE.differentiableOn.inv (fun p _ => hE₀ p))
  obtain ⟨N, hN, hNF, hNH⟩ := compactParameterEntireContinuation F H σ (1 - σ) hF hH (by
    refine ⟨min δ 1, lt_min hδ one_pos, fun z hz => ?_⟩
    have hzP : z ∈ P := ball_subset_ball ((min_le_right _ _).trans (by norm_num)) hz
    obtain ⟨U, V, hU, hV, ⟨τ, hτ⟩, hUV⟩ := hInit z (ball_subset_ball (min_le_left _ _) hz)
    have hfix : Differentiable ℂ (fun s : ℂ => (z, s)) :=
      (differentiable_const z).prodMk differentiable_id
    have hUR : EqOn U (fun s => F (z, s)) R :=
      Langlands.GeneralDirichlet.eqOn_halfPlane hU.differentiableOn
        (hF.comp hfix.differentiableOn (fun _ hs => ⟨hzP, hs⟩)) (fun s hs => (hτ s hs).1)
    have hVR : EqOn V (fun s => G (z, s)) R :=
      Langlands.GeneralDirichlet.eqOn_halfPlane hV.differentiableOn
        (hG.comp hfix.differentiableOn (fun _ hs => ⟨hzP, hs⟩)) (fun s hs => (hτ s hs).2)
    refine ⟨U, hU, hUR, fun s hs => ?_⟩
    change U s = G (z, ρ s) / E (z, s)
    apply (eq_div_iff (hE₀ (z, s))).2
    exact ((mul_comm _ _).trans (hUV s).symm).trans (hVR ((hρ s).2 hs)))
  let Nd (s : ℂ) := E (1, ρ s) * N (ρ s)
  have hNd : Differentiable ℂ Nd :=
    (hE.comp ((differentiable_const (1 : ℂ)).prodMk hρd)).mul (hN.comp hρd)
  refine ⟨N, Nd, hN, hNd, ⟨σ, fun s hs => ⟨hNF hs, ?_⟩⟩, fun s => ?_⟩
  · have hs' : ρ (ρ s) ∈ R := by
      rw [hρρ]
      exact hs
    have h : N (ρ s) = H (1, ρ s) := hNH ((hρ (ρ s)).1 hs')
    change E (1, ρ s) * N (ρ s) = G (1, s)
    rw [h]
    simp only [H, hρρ]
    rw [mul_div_cancel₀ _ (hE₀ (1, ρ s))]
  · change E (1, ρ (ρ s)) * N (ρ (ρ s)) = _
    rw [hρρ]

end Langlands.Analysis.SeveralComplex
