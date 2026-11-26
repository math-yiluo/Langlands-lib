import Langlands.Global.RankinSelberg.RealUniformContinuationReduction
import Mathlib.Analysis.Complex.Convex

/-! # Entire real normalizations from overlapping half-planes -/

noncomputable section

open Filter Set
open scoped Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open Langlands.LocalFactor

private theorem meromorphic_eq_nhdsNE {f g : ℂ → ℂ} {U V : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U)
    (hV : IsOpen V) (hVU : V ⊆ U) {z : ℂ} (hz : z ∈ V) (he : EqOn f g V) :
    ∀ w ∈ U, f =ᶠ[𝓝[≠] w] g := by
  have htop : meromorphicOrderAt (f - g) z = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hz)] with t ht
    exact sub_eq_zero.mpr (he ht)
  intro w hw
  exact (eventuallyEq_iff_sub).mpr (meromorphicOrderAt_eq_top_iff.mp
    ((hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hU (hVU hz) hw htop))

private theorem agrees_near_right {f g : ℂ → ℂ} (hf : MeromorphicOn f univ)
    {a b : ℝ} (hg : DifferentiableOn ℂ g {s : ℂ | a < s.re})
    (hfg : ∀ s : ℂ, b < s.re → f s = g s) :
    ∀ w : ℂ, a < w.re → f =ᶠ[𝓝[≠] w] g := by
  let V : Set ℂ := {s : ℂ | max a b < s.re}
  let z : ℂ := ((max a b + 1 : ℝ) : ℂ)
  have hz : z ∈ V := by
    change max a b < ((max a b + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    exact lt_add_one _
  have hU : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine meromorphic_eq_nhdsNE (V := V) (fun w _ => hf w (mem_univ _))
    (hg.analyticOnNhd hU).meromorphicOn
    (convex_halfSpace_re_gt a).isPreconnected (isOpen_lt continuous_const Complex.continuous_re)
    (fun w hs => show a < w.re from (le_max_left _ _).trans_lt hs) hz
    (fun w hs => hfg w ((le_max_right _ _).trans_lt hs))

/-- A meromorphic continuation package yields entire normalizations when the two
integrals are holomorphic on right half-planes whose thresholds sum to less than one. -/
def RealOverlappingNormalizationStatement : Prop :=
  ∀ (Z Zd : ℂ → ℂ) (D Dd : ReciprocalEntire) (E : ℂ → ℂ) (sign : ℂ) (a b : ℝ),
    a + b < 1 → sign ≠ 0 → Differentiable ℂ E → (∀ s, E s ≠ 0) →
    DifferentiableOn ℂ Z {s : ℂ | a < s.re} →
    DifferentiableOn ℂ Zd {s : ℂ | b < s.re} →
    ContinuationPackage Z Zd (fun s => (D.denominator s)⁻¹)
      (fun s => (Dd.denominator s)⁻¹) E sign →
    ∃ N Nd : ℂ → ℂ, Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      (∀ s, a < s.re → N s = D.denominator s * Z s) ∧
      (∀ s, b < s.re → Nd s = Dd.denominator s * Zd s) ∧
      ∀ s, Nd (1 - s) = sign * E s * N s

theorem realOverlappingNormalization : RealOverlappingNormalizationStatement := by
  intro Z Zd D Dd E sign a b hab hsign hE hE₀ hZ hZd ⟨τ, M, Md, hM, hMd, hMZ, hMdZ, hEq⟩
  let U : Set ℂ := {s : ℂ | a < s.re}
  let V : Set ℂ := {s : ℂ | s.re < 1 - b}
  let F (s : ℂ) := D.denominator s * Z s
  let G (s : ℂ) := (Dd.denominator (1 - s) * Zd (1 - s)) / (sign * E s)
  let ρ (s : ℂ) := 1 - s
  have hρ : Differentiable ℂ ρ := differentiable_id.const_sub 1
  have hρre (s : ℂ) : (ρ s).re = 1 - s.re := by simp [ρ, Complex.sub_re]
  have hρV (s : ℂ) (hs : s ∈ V) : b < (ρ s).re := by
    rw [hρre]
    exact lt_sub_comm.mp hs
  have hUV {s : ℂ} (hs : s ∉ U) : s ∈ V := by
    change ¬ a < s.re at hs
    change s.re < 1 - b
    linarith [le_of_not_gt hs]
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hVo : IsOpen V := isOpen_lt Complex.continuous_re continuous_const
  have hF : DifferentiableOn ℂ F U := D.entire.differentiableOn.mul hZ
  have hG : DifferentiableOn ℂ G V :=
    (((Dd.entire.comp hρ).differentiableOn).mul
      (hZd.comp hρ.differentiableOn fun s hs => hρV s hs)).div
      (hE.const_mul sign).differentiableOn (fun s _ => mul_ne_zero hsign (hE₀ s))
  have hMdρ : MeromorphicOn (fun s => Md (ρ s)) univ := fun s _ =>
    (hMd (ρ s) (mem_univ _)).comp_analyticAt (hρ.analyticAt s)
  have hZdρ : DifferentiableOn ℂ (fun s => Zd (ρ s)) V :=
    hZd.comp hρ.differentiableOn fun s hs => hρV s hs
  have hMdZd : ∀ s ∈ V, (fun w => Md (ρ w)) =ᶠ[𝓝[≠] s] fun w => Zd (ρ w) := by
    let V' : Set ℂ := {s : ℂ | s.re < 1 - max b τ}
    let z : ℂ := ((-max b τ : ℝ) : ℂ)
    have hz : z ∈ V' := by
      change ((-max b τ : ℝ) : ℂ).re < 1 - max b τ
      rw [Complex.ofReal_re]
      linarith
    refine meromorphic_eq_nhdsNE (V := V') (fun w _ => hMdρ w (mem_univ _))
      (hZdρ.analyticOnNhd hVo).meromorphicOn
      (convex_halfSpace_re_lt (1 - b)).isPreconnected (isOpen_lt Complex.continuous_re continuous_const)
      (fun w hw => show w.re < 1 - b from lt_of_lt_of_le hw (sub_le_sub_left (le_max_left _ _) _))
      hz ?_
    intro w hw
    apply Eq.symm
    apply hMdZ
    rw [hρre]
    exact (le_max_right _ _).trans_lt (lt_sub_comm.mp hw)
  have hFG (s : ℂ) (hsU : s ∈ U) (hsV : s ∈ V) : F s = G s := by
    have hMN := agrees_near_right hM hZ (fun s hs => (hMZ s hs).symm) s hsU
    have htend : Tendsto ρ (𝓝[≠] s) (𝓝[≠] (ρ s)) := by
      refine tendsto_nhdsWithin_iff.2
        ⟨hρ.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      have hne : ∀ᶠ w in 𝓝[≠] s, w ≠ s := self_mem_nhdsWithin
      filter_upwards [hne] with w hw
      intro he
      change 1 - w = 1 - s at he
      exact hw (sub_right_inj.mp he)
    have hDE : ∀ᶠ w in 𝓝[≠] s, Dd.denominator (ρ w) ≠ 0 :=
      htend.eventually (Dd.denominator_eventually_ne_zero (ρ s))
    have heq : F =ᶠ[𝓝[≠] s] G := by
      filter_upwards [hEq.filter_mono (nhdsNE_le_codiscrete s), hMN, hMdZd s hsV,
        D.denominator_eventually_ne_zero s, hDE]
        with w he hmw hmdw hdw hddw
      change (D.denominator w)⁻¹ * Md (1 - w) =
        sign * E w * (Dd.denominator (1 - w))⁻¹ * M w at he
      change Dd.denominator (1 - w) ≠ 0 at hddw
      change Md (1 - w) = Zd (1 - w) at hmdw
      rw [hmw, hmdw] at he
      change D.denominator w * Z w = (Dd.denominator (1 - w) * Zd (1 - w)) / (sign * E w)
      apply (eq_div_iff (mul_ne_zero hsign (hE₀ w))).2
      field_simp [hdw, hddw] at he
      linear_combination -he
    have hFc := (hF.differentiableAt (hUo.mem_nhds hsU)).continuousAt.tendsto
    have hGc := (hG.differentiableAt (hVo.mem_nhds hsV)).continuousAt.tendsto
    exact tendsto_nhds_unique (hFc.mono_left nhdsWithin_le_nhds)
      ((tendsto_congr' heq).2 (hGc.mono_left nhdsWithin_le_nhds))
  classical
  let N (s : ℂ) := if s ∈ U then F s else G s
  have hNU : EqOn N F U := fun _ hs => ite_eq_left hs
  have hNV : EqOn N G V := by
    intro s hs
    by_cases hsU : s ∈ U
    · exact (ite_eq_left hsU).trans (hFG s hsU hs)
    · exact ite_eq_right hsU
  have hN : Differentiable ℂ N := by
    intro s
    by_cases hs : s ∈ U
    · refine (hF.differentiableAt (hUo.mem_nhds hs)).congr_of_eventuallyEq ?_
      filter_upwards [hUo.mem_nhds hs] with w hw
      exact hNU hw
    · have hv := hUV hs
      refine (hG.differentiableAt (hVo.mem_nhds hv)).congr_of_eventuallyEq ?_
      filter_upwards [hVo.mem_nhds hv] with w hw
      exact hNV hw
  let Nd (s : ℂ) := sign * E (ρ s) * N (ρ s)
  have hNd : Differentiable ℂ Nd := ((hE.comp hρ).const_mul sign).mul (hN.comp hρ)
  refine ⟨N, Nd, hN, hNd, fun s hs => hNU hs, fun s hs => ?_, fun s => ?_⟩
  · have hs' : ρ s ∈ V := by change (ρ s).re < 1 - b; rw [hρre]; linarith
    change sign * E (ρ s) * N (ρ s) = _
    rw [hNV hs']
    change sign * E (ρ s) * ((Dd.denominator (1 - ρ s) * Zd (1 - ρ s)) / (sign * E (ρ s))) = _
    rw [mul_div_cancel₀ _ (mul_ne_zero hsign (hE₀ _)), show 1 - ρ s = s by simp [ρ]]
  · change sign * E (1 - (1 - s)) * N (1 - (1 - s)) = _
    rw [sub_sub_cancel]

end Langlands.Global.RankinSelbergGlobal.RealJacquet
