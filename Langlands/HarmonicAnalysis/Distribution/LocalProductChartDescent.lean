import Langlands.HarmonicAnalysis.Distribution.FullTestChartTransport
import Langlands.HarmonicAnalysis.Distribution.ProductJetCovariance

/-! # Local vanishing from leading-coefficient vanishing in a product chart -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {X E W F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U U₀ : Opens E} {V V₀ : Opens W}
  (e : OpenPartialHomeomorph (E × W) X)
  (he' : ContDiffOn ℝ ∞ e.symm e.target)

/-- Express a full-space distribution in a smooth chart and restrict to an
open product contained in the chart source. -/
def restrictProductChartDistribution (_ : productTestDomain U V ≤ chartSource e)
    (D : 𝓓'((⊤ : Opens X), F)) : 𝓓'(productTestDomain U V, F) :=
  (chartFullDistribution e he' D).comp (TestFunction.monoCLM ℝ)

theorem isVanishingOn_restrictProductChartDistribution
    (hUV : productTestDomain U V ≤ chartSource e) (D : 𝓓'((⊤ : Opens X), F))
    {s : Set X} {t : Set (E × W)} (hD : Distribution.IsVanishingOn D s)
    (hst : e '' (t ∩ (productTestDomain U V : Set (E × W))) ⊆ s) :
    Distribution.IsVanishingOn (restrictProductChartDistribution e he' hUV D) t := by
  intro f hf
  let g : 𝓓(chartSource e, ℝ) := TestFunction.monoCLM ℝ f
  have hg : (g : E × W → ℝ) = f := by simp [g, hUV]
  change D (chartTestToFullCLM e he' g) = 0
  apply hD
  refine (tsupport_chartTestToFullCLM_subset e he' g).trans ((image_mono ?_).trans hst)
  rw [hg]
  exact subset_inter hf f.tsupport_subset

theorem restrictProductChartDistribution_mono
    (hUV : productTestDomain U V ≤ chartSource e)
    (h : productTestDomain U₀ V₀ ≤ productTestDomain U V) (D : 𝓓'((⊤ : Opens X), F)) :
    (restrictProductChartDistribution e he' hUV D).comp
        (TestFunction.monoCLM ℝ (Ω₁ := productTestDomain U₀ V₀) (n₁ := ⊤)) =
      restrictProductChartDistribution e he' (h.trans hUV) D := by
  apply DFunLike.ext
  intro f
  let g : 𝓓(productTestDomain U V, ℝ) := TestFunction.monoCLM ℝ f
  have hg : (g : E × W → ℝ) = f := by simp [g, h]
  have hmono : (TestFunction.monoCLM ℝ g : 𝓓(chartSource e, ℝ)) =
      TestFunction.monoCLM ℝ f := by
    ext z
    have hf' : ((TestFunction.monoCLM ℝ f : 𝓓(chartSource e, ℝ)) : E × W → ℝ) = f := by
      simp [h.trans hUV]
    have hg' : ((TestFunction.monoCLM ℝ g : 𝓓(chartSource e, ℝ)) : E × W → ℝ) = g := by
      simp [hUV]
    exact congrFun (hg'.trans (hg.trans hf'.symm)) z
  change chartFullDistribution e he' D (TestFunction.monoCLM ℝ g) =
    chartFullDistribution e he' D (TestFunction.monoCLM ℝ f)
  rw [hmono]

/-- Vanishing of the restriction in coordinates implies vanishing of the
original distribution on the chart image. -/
theorem isVanishingOn_chartImage_of_restrictProductChartDistribution_eq_zero
    (he : ContDiffOn ℝ ∞ e e.source)
    (hUV : productTestDomain U V ≤ chartSource e) (D : 𝓓'((⊤ : Opens X), F))
    (hzero : restrictProductChartDistribution e he' hUV D = 0) :
    Distribution.IsVanishingOn D (e '' (productTestDomain U V : Set (E × W))) := by
  intro f hf
  have hft : tsupport f ⊆ e.target := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hf hx
    exact e.map_source (hUV hz)
  let f' : 𝓓(chartTarget e, ℝ) := ⟨f, f.contDiff, f.hasCompactSupport, hft⟩
  let g := pullbackChartTestCLM e he f'
  have hg : tsupport g ⊆ productTestDomain U V := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := tsupport_pullbackChartTestCLM_subset e he f' hz
    obtain ⟨w, hw, rfl⟩ := hf hx
    rwa [e.left_inv (hUV hw)]
  let g' : 𝓓(productTestDomain U V, ℝ) := ⟨g, g.contDiff, g.hasCompactSupport, hg⟩
  have hmono : (TestFunction.monoCLM ℝ g' : 𝓓(chartSource e, ℝ)) = g := by
    ext z
    have h : ((TestFunction.monoCLM ℝ g' : 𝓓(chartSource e, ℝ)) : E × W → ℝ) = g' := by
      simp [hUV]
    exact congrFun h z
  have heq : chartTestToFullCLM e he' g = f := by
    ext x
    by_cases hx : x ∈ e.target
    · rw [chartTestToFullCLM_apply_of_mem e he' g hx]
      change pullbackChartTestCLM e he f' (e.symm x) = f x
      rw [pullbackChartTestCLM_apply_of_mem e he f' (e.map_target hx), e.right_inv hx]
      rfl
    · rw [chartTestToFullCLM_apply_of_notMem e he' g hx]
      exact (image_eq_zero_of_notMem_tsupport (fun hy => hx (hft hy))).symm
  have h : restrictProductChartDistribution e he' hUV D g' = 0 := by rw [hzero]; rfl
  change D (chartTestToFullCLM e he' (TestFunction.monoCLM ℝ g')) = 0 at h
  rwa [hmono, heq] at h

/-- A stratum contained in a zero section can be eliminated locally by
showing that the leading coefficient vanishes at every available order. -/
theorem isVanishingOn_chartImage_of_leading_coefficients_eq_zero [FiniteDimensional ℝ W]
    (he : ContDiffOn ℝ ∞ e e.source)
    (hUV : productTestDomain U V ≤ chartSource e) (D : 𝓓'((⊤ : Opens X), F))
    {s : Set X} (hD : Distribution.IsVanishingOn D s)
    (hs : e '' ({z : E × W | z.2 ≠ 0} ∩ (productTestDomain U V : Set (E × W))) ⊆ s)
    {K : Compacts (E × W)} (hK : (K : Set (E × W)) ⊆ productTestDomain U V)
    (hK₀ : (productTestDomain U₀ V₀ : Set (E × W)) ⊆ K)
    (χ : 𝓓(V₀, ℝ)) (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1)
    (hcoeff : ∀ i,
      HasTransverseJetOrder (restrictProductChartDistribution e he'
        ((hK₀.trans hK).trans hUV) D) i →
      transverseProductJetCoefficient (restrictProductChartDistribution e he'
        ((hK₀.trans hK).trans hUV) D) χ i = 0) :
    Distribution.IsVanishingOn D (e '' (productTestDomain U₀ V₀ : Set (E × W))) := by
  let T := restrictProductChartDistribution e he' hUV D
  let T₀ := restrictProductChartDistribution e he' ((hK₀.trans hK).trans hUV) D
  have hT : Distribution.IsVanishingOn T {z : E × W | z.2 ≠ 0} :=
    isVanishingOn_restrictProductChartDistribution e he' hUV D hD hs
  have hord : HasTransverseJetOrder T₀ (smoothDistributionCompactOrder T hK) := by
    have h := hasTransverseJetOrder_comp_monoCLM T hT hK hK₀
    change HasTransverseJetOrder
      ((restrictProductChartDistribution e he' hUV D).comp (TestFunction.monoCLM ℝ))
      (smoothDistributionCompactOrder T hK) at h
    rw [restrictProductChartDistribution_mono e he' hUV (hK₀.trans hK) D] at h
    exact h
  have hzero (i : ℕ) (hi : HasTransverseJetOrder T₀ i) : T₀ = 0 := by
    induction i with
    | zero => exact distribution_eq_zero_of_coefficient_zero_at_order_zero T₀ hi χ hχ (hcoeff 0 hi)
    | succ i ih =>
      exact ih (hasTransverseJetOrder_of_coefficient_eq_zero T₀ i hi χ hχ (hcoeff (i + 1) hi))
  exact isVanishingOn_chartImage_of_restrictProductChartDistribution_eq_zero e he' he
    ((hK₀.trans hK).trans hUV) D (hzero _ hord)

end Langlands.HarmonicAnalysis
