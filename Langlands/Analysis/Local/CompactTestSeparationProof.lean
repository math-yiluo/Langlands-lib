import Langlands.Analysis.Local.CompactTestSeparationStatement
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Separation.PerfectlyNormal
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

universe u

namespace Langlands.Analysis

open MeasureTheory Filter Function Set Topology
open scoped CompactlySupported

theorem compactTestSeparation : CompactTestSeparationStatement.{u} := by
  intro X _ _ _ _ _ _ μ F hF
  refine ⟨?_, ?_⟩
  · intro f
    exact hF.integrable_smul_left_of_hasCompactSupport f.continuous.star
      (f.hasCompactSupport.comp_left (g := star) (star_zero ℂ))
  · constructor
    · intro hz f
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with x hx
      simp [hx]
    · intro h
      apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hF
      intro K hK
      obtain ⟨ρ, hρK, _, hρc, hρrange⟩ :=
        exists_continuous_one_zero_of_isCompact_of_isGδ hK hK.isClosed.isGδ
          isClosed_empty (disjoint_empty K)
      let g : ℕ → X → ℝ := fun n x => (ρ x) ^ (n + 1)
      have hgc (n : ℕ) : Continuous (g n) := ρ.continuous.pow _
      have hgcs (n : ℕ) : HasCompactSupport (g n) := by
        exact hρc.comp_left (g := fun r : ℝ => r ^ (n + 1)) (by simp)
      have hgzero (n : ℕ) : (∫ x, g n x • F x ∂μ) = 0 := by
        let f : C_c(X, ℂ) :=
          ⟨⟨fun x => (g n x : ℂ), Complex.continuous_ofReal.comp (hgc n)⟩,
            (hgcs n).comp_left Complex.ofReal_zero⟩
        have hf := h f
        simpa [f, Complex.real_smul] using hf
      have hgbound (n : ℕ) (x : X) : ‖g n x‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (pow_nonneg (hρrange x).1 _)]
        exact pow_le_one₀ (hρrange x).1 (hρrange x).2
      let B : X → ℝ := (tsupport ρ).indicator (fun x => ‖F x‖)
      have hB : Integrable B μ := by
        rw [integrable_indicator_iff hρc.measurableSet]
        exact (hF.integrableOn_isCompact hρc).norm
      have hA (n : ℕ) : AEStronglyMeasurable (fun x => g n x • F x) μ :=
        (hgc n).aestronglyMeasurable.smul hF.aestronglyMeasurable
      have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖g n x • F x‖ ≤ B x := by
        filter_upwards with x
        rw [norm_smul]
        apply le_indicator_apply
        · intro _
          exact mul_le_of_le_one_left (norm_nonneg _) (hgbound n x)
        · intro hx
          have hρzero : ρ x = 0 := by
            by_contra hn
            exact hx (subset_tsupport ρ hn)
          simp [g, hρzero]
      have hlim : ∀ᵐ x ∂μ,
          Tendsto (fun n => g n x • F x) atTop (𝓝 (K.indicator F x)) := by
        filter_upwards with x
        by_cases hx : x ∈ K
        · have hρone : ρ x = 1 := by
            have := congrArg (fun A : Set X => x ∈ A) hρK
            simpa only [mem_preimage, mem_singleton_iff] using this.mp hx
          simp [g, hρone, indicator_of_mem hx]
        · have hρne : ρ x ≠ 1 := by
            intro he
            apply hx
            rw [hρK]
            exact he
          have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (hρrange x).1
            (lt_of_le_of_ne (hρrange x).2 hρne)
          have ht' : Tendsto (fun n : ℕ => g n x) atTop (𝓝 (0 : ℝ)) :=
            (tendsto_add_atTop_iff_nat 1).mpr ht
          simpa only [zero_smul, indicator_of_notMem hx] using ht'.smul_const (F x)
      have hconv := tendsto_integral_of_dominated_convergence B hA hB hbound hlim
      rw [integral_indicator hK.measurableSet] at hconv
      have hz : (0 : ℂ) = ∫ x in K, F x ∂μ := by
        simpa only [hgzero, tendsto_const_nhds_iff] using hconv
      exact hz.symm

end Langlands.Analysis
