import Mathlib.Analysis.Distribution.Distribution

/-! # Smooth cutoff multiplication between real test function spaces -/

noncomputable section

open Set TopologicalSpace
open scoped BoundedContinuousFunction ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)

private def cutoffSupport (K : Compacts E) : Compacts E :=
  ⟨(K : Set E) ∩ tsupport χ, K.isCompact.inter_right (isClosed_tsupport χ)⟩

private def cutoffCompactTest (K : Compacts E) (φ : 𝓓_{K}(E, ℝ)) :
    𝓓_{cutoffSupport (χ := χ) K}(E, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset (φ.contDiff.mul hχ) <| by
    intro x hx
    exact ⟨φ.support_subset (fun h => hx (by simp [h])),
      subset_tsupport χ (fun h => hx (by simp [h]))⟩

private def cutoffCompactTestCLM (K : Compacts E) :
    𝓓_{K}(E, ℝ) →L[ℝ] 𝓓_{cutoffSupport (χ := χ) K}(E, ℝ) where
  toFun := cutoffCompactTest hχ K
  map_add' := by
    intro φ ψ
    ext x
    change (φ x + ψ x) * χ x = φ x * χ x + ψ x * χ x
    exact add_mul _ _ _
  map_smul' := by
    intro c φ
    ext x
    change (c * φ x) * χ x = c * (φ x * χ x)
    exact mul_assoc _ _ _
  cont := by
    apply (ContDiffMapSupportedIn.continuous_iff_comp _).mpr
    intro i
    let m : 𝓓_{K}(E, ℝ) →L[ℝ] 𝓓_{K}(E, ℝ) :=
      ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hχ
    have hm := (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (K := K) (F := ℝ) i).continuous.comp
      m.continuous
    apply hm.congr
    intro φ
    apply BoundedContinuousFunction.ext
    intro x
    change ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (m φ) x =
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (cutoffCompactTest hχ K φ) x
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rfl

variable (Ω : Opens E) (hs : tsupport χ ⊆ Ω)

/-- Multiply a real smooth test by a smooth scalar cutoff supported in `Ω`,
viewing the product as a test on `Ω`. -/
def cutoffTestCLM : 𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.limitCLM ℝ
    (fun φ => ⟨fun x => φ x * χ x, φ.contDiff.mul hχ, φ.hasCompactSupport.mul_right,
      tsupport_mul_subset_right.trans hs⟩)
    (fun K _ => (TestFunction.ofSupportedInCLM ℝ
        (show (cutoffSupport (χ := χ) K : Set E) ⊆ Ω from inter_subset_right.trans hs)).comp
      (cutoffCompactTestCLM hχ K))
    (fun _ _ _ => rfl)

@[simp]
theorem cutoffTestCLM_apply (φ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    cutoffTestCLM hχ Ω hs φ x = φ x * χ x := rfl

end Langlands.HarmonicAnalysis
