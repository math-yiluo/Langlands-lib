import Langlands.HarmonicAnalysis.Distribution.RealMatrixConjugationDerivative

/-! # Differentiating scalar evaluations of smoothly parameterized tests -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : Compacts E} {s : Opens ℝ} {h : ℝ × E → F}

private theorem timeDifferenceQuotient_zero_outside (hh : ContDiff ℝ ∞ h)
    (h0 : (0 : ℝ) ∈ s) (hs : ∀ t ∈ s, ∀ x ∉ K, h (t, x) = 0) :
    ∀ t ∈ s, ∀ x ∉ K, smoothTimeDifferenceQuotient h (t, x) = 0 := by
  intro t ht x hx
  by_cases hn : t = 0
  · subst t
    have he : (fun r : ℝ => h (r, x)) =ᶠ[𝓝 0] (fun _ => (0 : F)) := by
      filter_upwards [s.isOpen.mem_nhds h0] with r hr
      exact hs r hr x hx
    have hc : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
    have hd := ((hh.differentiable (by simp) (0, x)).hasFDerivAt.comp_hasDerivAt 0 hc).deriv
    rw [smoothTimeDifferenceQuotient_zero, ← hd]
    rw [show (h ∘ fun r : ℝ => (r, x)) = (fun r => h (r, x)) from rfl, he.deriv_eq]
    simp
  · have hz := smul_smoothTimeDifferenceQuotient hh t x
    rw [hs t ht x hx, hs 0 h0 x hx, sub_zero] at hz
    exact (smul_eq_zero.mp hz).resolve_left hn

/-- The derivative of a scalar response to a jointly smooth family of
fixed-support tests is the response to the derivative test. -/
theorem eval_compactTestTimeDerivative_of_hasDerivAt (hh : ContDiff ℝ ∞ h)
    (h0 : (0 : ℝ) ∈ s) (hs : ∀ t ∈ s, ∀ x ∉ K, h (t, x) = 0)
    (T : 𝓓_{K}(E, F) →L[ℝ] G) (g : ℝ → G) (v : G) (hg : HasDerivAt g v 0)
    (hT : ∀ t : s, T (compactTestFamily hh hs t) = g t) :
    T (compactTestTimeDerivative hh h0 hs) = v := by
  classical
  let Q := compactTestFamily (contDiff_smoothTimeDifferenceQuotient hh)
    (timeDifferenceQuotient_zero_outside hh h0 hs)
  let U (t : ℝ) : G := if ht : t ∈ s then T (Q ⟨t, ht⟩) else 0
  have hU : ContinuousOn U s := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (s : Set ℝ).domRestrict U = T ∘ Q := by
      funext t
      exact dite_eq_left t.property
    rw [he]
    exact T.continuous.comp (continuous_compactTestFamily _ _)
  have hlim : Tendsto U (𝓝[≠] (0 : ℝ)) (𝓝 (T (compactTestTimeDerivative hh h0 hs))) := by
    have h : Tendsto U (𝓝[≠] (0 : ℝ)) (𝓝 (U 0)) :=
      (hU.continuousAt (s.isOpen.mem_nhds h0)).tendsto.mono_left nhdsWithin_le_nhds
    rwa [show U 0 = T (compactTestTimeDerivative hh h0 hs) from dite_eq_left h0] at h
  have heq : U =ᶠ[𝓝[≠] (0 : ℝ)] fun t => t⁻¹ • (g t - g 0) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (s.isOpen.mem_nhds h0), self_mem_nhdsWithin]
      with t ht ht₀
    have ht₀' : t ≠ 0 := mem_compl_singleton_iff.mp ht₀
    have he : t • Q ⟨t, ht⟩ = compactTestFamily hh hs ⟨t, ht⟩ -
        compactTestFamily hh hs ⟨0, h0⟩ := by
      ext x
      exact smul_smoothTimeDifferenceQuotient hh t x
    have hz := congrArg T he
    rw [map_smul, map_sub, hT, hT] at hz
    rw [show U t = T (Q ⟨t, ht⟩) from dite_eq_left ht, ← hz, smul_smul,
      inv_mul_cancel₀ ht₀', one_smul]
  have hg' : Tendsto (fun t : ℝ => t⁻¹ • (g t - g 0)) (𝓝[≠] 0) (𝓝 v) := by
    simpa only [zero_add] using hg.tendsto_slope_zero
  exact tendsto_nhds_unique hlim (hg'.congr' heq.symm)

end Langlands.HarmonicAnalysis
