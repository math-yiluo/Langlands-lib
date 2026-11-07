import Langlands.Analysis.SmoothCompactKernelConvolutionStatement
import Langlands.Analysis.CompactManifoldWeightedIntegralProof
import Mathlib.Topology.Algebra.Group.Compact

noncomputable section

universe uV uG uE

namespace Langlands.Analysis

open MeasureTheory Set
open scoped Manifold ContDiff Pointwise

/-- Compact support yields a fixed compact integration set near each parameter. -/
theorem smoothCompactKernelConvolution :
    SmoothCompactKernelConvolutionStatement.{uV,uG,uE} := by
  intro V _ _ G _ _ _ _ _ _ _ _ _ E _ _ _ μ _ w κ hκ hκc
  constructor
  · intro p
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hκ.continuous.comp (continuous_inv.mul continuous_const)).smul w.continuous
    · exact (hκc.comp_homeomorph
        ((Homeomorph.inv G).trans (Homeomorph.mulRight p))).smul_right
  · intro p₀
    obtain ⟨D, hDc, hD⟩ := exists_compact_mem_nhds p₀
    let K : Set G := D * (tsupport κ)⁻¹
    have hKc : IsCompact K := hDc.mul hκc.inv
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    let ν : Measure G := μ.restrict K
    let : IsFiniteMeasure ν := ⟨by
      simpa only [ν, Measure.restrict_apply_univ] using hKc.measure_lt_top (μ := μ)⟩
    let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    let j : C(K, G) := ⟨Subtype.val, continuous_subtype_val⟩
    let wi : C(K, E) := w.comp j
    let k : G × G → ℂ := fun q => κ (q.2⁻¹ * q.1)
    have hk : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℂ) ∞ k :=
      hκ.comp (contMDiff_snd.inv.mul contMDiff_fst)
    have hs := (compactManifoldWeightedIntegral K V G V G E
      (ν.comap Subtype.val) wi j k hk).2
    apply (hs p₀).congr_of_eventuallyEq
    filter_upwards [hD] with p hp
    change (∫ y, κ (y⁻¹ * p) • w y ∂μ) =
      (∫ y : K, κ (y.val⁻¹ * p) • w y.val ∂(ν.comap Subtype.val))
    symm
    rw [integral_subtype_comap hKm (fun y => κ (y⁻¹ * p) • w y)]
    change (∫ y in K, κ (y⁻¹ * p) • w y ∂(μ.restrict K)) = _
    rw [Measure.restrict_restrict hKm, inter_self]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hz : κ (y⁻¹ * p) = 0 := by
      by_contra hne
      have hyS : y⁻¹ * p ∈ tsupport κ :=
        subset_tsupport κ (Function.mem_support.mpr hne)
      apply hy
      exact Set.mem_mul.mpr ⟨p, hp, (y⁻¹ * p)⁻¹,
        by simpa using hyS, by simp [mul_inv_rev, ← mul_assoc]⟩
    rw [hz, zero_smul]

end Langlands.Analysis
