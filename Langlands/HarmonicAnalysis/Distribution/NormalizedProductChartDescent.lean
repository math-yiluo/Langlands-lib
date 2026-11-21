import Langlands.HarmonicAnalysis.Distribution.LocalProductChartDescent
import Langlands.HarmonicAnalysis.Distribution.NormalizedChartDistribution

/-! # Support and transverse order in Jacobian-normalized product charts -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E W X F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U U₀ : Opens E} {V V₀ : Opens W}
  {e : OpenPartialHomeomorph (E × W) X}
  (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
  (L : (E × W) ≃L[ℝ] X) (hUV : productTestDomain U V ≤ chartSource e)

/-- Restrict a distribution to a chart product after removing the chart's
Jacobian density from the tests. -/
def normalizedProductChartDistribution (D : 𝓓'((⊤ : Opens X), F)) :
    𝓓'(productTestDomain U V, F) :=
  jacobianNormalizedChartDistribution he hei L hUV D

/-- Removing the Jacobian preserves the support condition of a chart restriction. -/
theorem isVanishingOn_normalizedProductChartDistribution (D : 𝓓'((⊤ : Opens X), F))
    {s : Set X} {t : Set (E × W)} (hD : Distribution.IsVanishingOn D s)
    (hst : e '' (t ∩ (productTestDomain U V : Set (E × W))) ⊆ s) :
    Distribution.IsVanishingOn (normalizedProductChartDistribution he hei L hUV D) t := by
  intro f hf
  let g := localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L hUV) f
  have hg : tsupport g ⊆ tsupport f := tsupport_mul_subset_left
  change restrictProductChartDistribution e hei hUV D g = 0
  exact isVanishingOn_restrictProductChartDistribution e hei hUV D hD hst g (hg.trans hf)

/-- Restriction to a smaller product commutes with Jacobian normalization. -/
theorem normalizedProductChartDistribution_mono
    (hsmall : productTestDomain U₀ V₀ ≤ productTestDomain U V) (D : 𝓓'((⊤ : Opens X), F)) :
    (normalizedProductChartDistribution he hei L hUV D).comp
        (TestFunction.monoCLM ℝ (Ω₁ := productTestDomain U₀ V₀) (n₁ := ⊤)) =
      normalizedProductChartDistribution he hei L (hsmall.trans hUV) D := by
  apply DFunLike.ext
  intro f
  let g := localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L (hsmall.trans hUV)) f
  have hg : (TestFunction.monoCLM ℝ g : 𝓓(productTestDomain U V, ℝ)) =
      localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L hUV)
        (TestFunction.monoCLM ℝ f) := by
    ext p
    have hm (φ : 𝓓(productTestDomain U₀ V₀, ℝ)) :
        ((TestFunction.monoCLM ℝ φ : 𝓓(productTestDomain U V, ℝ)) : E × W → ℝ) = φ := by
      simp [hsmall]
    rw [congrFun (hm g), localScalarMultiplierCLM_apply, localScalarMultiplierCLM_apply,
      congrFun (hm f)]
  change restrictProductChartDistribution e hei hUV D
      (localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L hUV)
        (TestFunction.monoCLM ℝ f)) =
    restrictProductChartDistribution e hei (hsmall.trans hUV) D g
  rw [← hg]
  exact DFunLike.congr_fun (restrictProductChartDistribution_mono e hei hUV hsmall D) g

/-- If the normalized restriction is zero, the raw restriction is zero as
well because multiplying a test by the Jacobian recovers its raw evaluation. -/
theorem restrictProductChartDistribution_eq_zero_of_normalized
    (D : 𝓓'((⊤ : Opens X), F)) (hz : normalizedProductChartDistribution he hei L hUV D = 0) :
    restrictProductChartDistribution e hei hUV D = 0 := by
  apply DFunLike.ext
  intro f
  have hf := jacobianNormalizedChartDistribution_eval_mul_jacobian he hei L hUV D f
  change normalizedProductChartDistribution he hei L hUV D
      (localScalarMultiplierCLM ((contDiffOn_chartAbsJacobian he hei L).mono hUV) f) =
    restrictProductChartDistribution e hei hUV D f at hf
  rw [hz, zero_apply] at hf
  exact hf.symm

/-- A normalized chart distribution supported on the zero section has finite
transverse order after restriction inside a fixed compact subset. -/
theorem hasTransverseJetOrder_normalizedProductChartDistribution
    (D : 𝓓'((⊤ : Opens X), F))
    (hzero : Distribution.IsVanishingOn (normalizedProductChartDistribution he hei L hUV D)
      {z : E × W | z.2 ≠ 0})
    {K : Compacts (E × W)} (hK : (K : Set (E × W)) ⊆ productTestDomain U V)
    (hK₀ : (productTestDomain U₀ V₀ : Set (E × W)) ⊆ K) :
    HasTransverseJetOrder (normalizedProductChartDistribution he hei L
      ((hK₀.trans hK).trans hUV) D)
      (smoothDistributionCompactOrder (normalizedProductChartDistribution he hei L hUV D) hK) := by
  rw [← normalizedProductChartDistribution_mono he hei L hUV (hK₀.trans hK) D]
  exact hasTransverseJetOrder_comp_monoCLM _ hzero hK hK₀

/-- A centered open product can be shrunk inside a compact subset of the
original product. -/
theorem exists_productTestDomain_subset_compact {p : E × W}
    (hp : p ∈ productTestDomain U V) :
    ∃ (U₀ : Opens E) (V₀ : Opens W) (K : Compacts (E × W)),
      p ∈ productTestDomain U₀ V₀ ∧
        (productTestDomain U₀ V₀ : Set (E × W)) ⊆ K ∧
        (K : Set (E × W)) ⊆ productTestDomain U V := by
  obtain ⟨K, hcompact, hpK, hK⟩ := exists_compact_between
    (isCompact_singleton (x := p)) (productTestDomain U V).isOpen
    (singleton_subset_iff.mpr hp)
  have hin : interior K ∈ 𝓝 (p.1, p.2) :=
    isOpen_interior.mem_nhds (hpK (mem_singleton p))
  obtain ⟨u, v, hu, hpu, hv, hpv, hprod⟩ := mem_nhds_prod_iff'.mp hin
  exact ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨K, hcompact⟩, ⟨hpu, hpv⟩, hprod.trans interior_subset, hK⟩

end Langlands.HarmonicAnalysis
