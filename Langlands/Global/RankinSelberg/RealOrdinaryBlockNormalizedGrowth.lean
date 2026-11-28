import Langlands.Global.RankinSelberg.RealOrdinaryStripGrowthReduction
import Langlands.Global.RankinSelberg.RealLocalUniformUnequalContinuationProof
import Langlands.Global.RankinSelberg.RealPlaceAscendingPrincipalSeriesReduction
import Langlands.Global.RankinSelberg.RealWeightedKernelReflection
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth
import Langlands.Global.RankinSelberg.ArchimedeanPairIdentityStripGrowth

/-! # Normalized reflection of exact real block coefficients -/

noncomputable section

open Filter Set Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealPrincipalSeries
open RealWeightedKernelReflection (pairReflectionFactor differentiable_pairReflectionFactor
  stripExpType_pairReflectionFactor)
open ArchimedeanRealPairIdentity (stripGrowth_of_stripExpType)
open CuspidalPairPartialGammaGlobal (eventually_codiscrete_one_sub)

private theorem eq_codiscrete_of_halfPlane {F G : ℂ → ℂ}
    (hF : MeromorphicOn F univ) (hG : MeromorphicOn G univ) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → F s = G s) : F =ᶠ[codiscrete ℂ] G := by
  let z : ℂ := (σ + 1 : ℝ)
  have hz : σ < z.re := by rw [Complex.ofReal_re]; linarith
  have hnear : ∀ᶠ s in 𝓝 z, σ < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hzero : (F - G) =ᶠ[𝓝[≠] z] 0 :=
    (hnear.filter_mono nhdsWithin_le_nhds).mono fun s hs => sub_eq_zero.mpr (h s hs)
  have ho := meromorphicOrderAt_eq_top_iff.mpr hzero
  refine eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr fun s => ?_
  have hs := (hF.sub hG).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ z) (mem_univ s) ho
  exact (eventuallyEq_iff_sub).mpr (meromorphicOrderAt_eq_top_iff.mp hs)

private theorem normalizedGrowth_of_primal {ds es dds ees : List RealBlock} {b : ℝˣ}
    {c : ℝ≥0} {hc : 0 < c} {sign : ℂ} {I Id : ℂ → ℂ}
    (hC : ContinuationPackage I Id (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
      (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
      (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign)
    (N : OrdinaryIntegralNormalization I (fun s => ((realPairLFactor ds es).denominator s)⁻¹))
    (hNg : HasStripExponentialGrowth N.value) (σd : ℝ)
    (hId : ContinuousOn Id {s : ℂ | σd < s.re}) :
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id := by
  obtain ⟨σ, M, Md, hM, _, hIM, hIdMd, hFE⟩ := hC
  obtain ⟨τ, hτ⟩ := N.eq_on_right
  obtain ⟨η, hη⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks ds es)
  let P := realPairLFactor ds es
  let Pd := realPairLFactor dds ees
  let E := pairReflectionFactor ds es b c hc sign
  let Nd (s : ℂ) := E (1 - s) * N.value (1 - s)
  have hN : Differentiable ℂ N.value := fun s => (N.analytic s (mem_univ s)).differentiableAt
  have hρ : Differentiable ℂ (fun s : ℂ => 1 - s) := differentiable_id.const_sub 1
  have hEd := differentiable_pairReflectionFactor ds es b c hc sign
  have hNd : Differentiable ℂ Nd := (hEd.comp hρ).mul (hN.comp hρ)
  have hNdg : HasStripExponentialGrowth Nd :=
    (stripGrowth_of_stripExpType (stripExpType_pairReflectionFactor ds es b c hc sign).comp_one_sub).mul
      hNg.comp_one_sub
  have hNI (s : ℂ) (hs : max τ η < s.re) : N.value s = P.denominator s * I s := by
    rw [hτ s ((le_max_left _ _).trans_lt hs)]
    change _ = P.denominator s * (N.value s * (P.denominator s)⁻¹)
    have hd : P.denominator s ≠ 0 := hη s ((le_max_right _ _).trans_lt hs)
    rw [mul_comm (N.value s), ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hPm : MeromorphicOn P.denominator univ := fun s _ => (P.entire.analyticAt s).meromorphicAt
  have hNM : N.value =ᶠ[codiscrete ℂ] P.denominator * M :=
    eq_codiscrete_of_halfPlane (fun s hs => (N.analytic s hs).meromorphicAt)
      (hPm.mul hM)
      (max (max τ η) σ) fun s hs => by
        rw [Pi.mul_apply, hNI s ((le_max_left _ _).trans_lt hs), hIM s ((le_max_right _ _).trans_lt hs)]
  have hNonzero (F : ReciprocalEntire) : ∀ᶠ s in codiscrete ℂ, F.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr F.denominator_eventually_ne_zero
  have hNdMd : Nd =ᶠ[codiscrete ℂ] Pd.denominator * Md :=
    eventually_codiscrete_one_sub (p := fun s => Nd (1 - s) = Pd.denominator (1 - s) * Md (1 - s)) (by
      filter_upwards [hFE, hNM, hNonzero P, eventually_codiscrete_one_sub (hNonzero Pd)]
        with s he hN' hp hpd
      change (P.denominator s)⁻¹ * Md (1 - s) = E s * (Pd.denominator (1 - s))⁻¹ * M s at he
      change P.denominator s ≠ 0 at hp
      change Pd.denominator (1 - s) ≠ 0 at hpd
      change N.value s = P.denominator s * M s at hN'
      change E (1 - (1 - s)) * N.value (1 - (1 - s)) = _
      rw [sub_sub_cancel, hN']
      field_simp at he
      linear_combination -he) |>.mono fun s hs => by simpa only [sub_sub_cancel, Pi.mul_apply] using hs
  refine ⟨N.value, Nd, hN, hNd, hNg, hNdg, ⟨max (max τ η) (max σ σd), fun s hs => ?_⟩,
    fun s => by change E (1 - (1 - s)) * N.value (1 - (1 - s)) = _; rw [sub_sub_cancel]; rfl⟩
  refine ⟨hNI s ((le_max_left _ _).trans_lt hs), ?_⟩
  have hO : IsOpen {z : ℂ | max σ σd < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hNear : ∀ᶠ z in 𝓝 s, max σ σd < (z : ℂ).re :=
    hO.mem_nhds ((le_max_right _ _).trans_lt hs)
  have hEq : Nd =ᶠ[𝓝[≠] s] fun z => Pd.denominator z * Id z := by
    filter_upwards [hNear.filter_mono nhdsWithin_le_nhds, hNdMd.filter_mono (nhdsNE_le_codiscrete s)] with z hz he
    rw [he, Pi.mul_apply, hIdMd z ((le_max_left _ _).trans_lt hz)]
  have hCont := Pd.entire.continuous.continuousAt.mul
    ((hId s ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))).continuousAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))))
  exact tendsto_nhds_unique_of_eventuallyEq hNd.continuous.continuousAt.continuousWithinAt
    hCont.continuousWithinAt hEq

private theorem normalizedGrowth_of_ascending {ds es : List RealBlock} {b : ℝˣ}
    {c : ℝ≥0} {hc : 0 < c} {sign : ℂ} {I Id : ℂ → ℂ}
    (hA : HasRealPairNormalizedGrowth (ascendingExpand ds) (ascendingExpand es)
      ((ascendingExpand ds).map RealLocalJacquet.dualBlock)
      ((ascendingExpand es).map RealLocalJacquet.dualBlock) b c hc sign I Id)
    (N : OrdinaryIntegralNormalization I (fun s => ((realPairLFactor ds es).denominator s)⁻¹)) :
    HasRealPairNormalizedGrowth ds es (ds.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) b c hc sign I Id := by
  have hp := ascendingExpand_perm ds
  have hq := ascendingExpand_perm es
  have hE : HasRealPairNormalizedGrowth (expand ds) (expand es)
      ((expand ds).map RealLocalJacquet.dualBlock) ((expand es).map RealLocalJacquet.dualBlock)
      b c hc sign I Id := by
    simpa only [HasRealPairNormalizedGrowth, realPairLFactor_perm hp hq,
      realPairLFactor_perm (hp.map RealLocalJacquet.dualBlock) (hq.map RealLocalJacquet.dualBlock),
      realPairEpsilon_perm hp hq] using hA
  have hC := continuationPackage_of_expand ds es b c hc hE.continuationPackage
  obtain ⟨M, hM, hMg, hR⟩ := hA.exists_meromorphic_stripGrowth
  have hNg := N.stripGrowth_realPair hM hMg hR
  obtain ⟨_, Nd, _, hNd, _, _, ⟨σ, hσ⟩, _⟩ := hE
  let Pd := realPairLFactor ((expand ds).map RealLocalJacquet.dualBlock)
    ((expand es).map RealLocalJacquet.dualBlock)
  obtain ⟨τ, hτ⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks
    ((expand ds).map RealLocalJacquet.dualBlock) ((expand es).map RealLocalJacquet.dualBlock))
  refine normalizedGrowth_of_primal hC N hNg (max σ τ) ?_
  have hq : ContinuousOn (fun s => Nd s / Pd.denominator s) {s : ℂ | max σ τ < s.re} :=
    hNd.continuous.continuousOn.div Pd.entire.continuous.continuousOn
      (fun s hs => hτ s ((le_max_right _ _).trans_lt hs))
  refine hq.congr fun s hs => ?_
  have he : Nd s = Pd.denominator s * Id s := (hσ s ((le_max_left _ _).trans_lt hs)).2
  have hd : Pd.denominator s ≠ 0 := hτ s ((le_max_right _ _).trans_lt hs)
  change Id s = Nd s / Pd.denominator s
  rw [he, mul_comm, mul_div_cancel_right₀ _ hd]

/-- Ordinary entire continuation for the exact real models gives the full normalized
pair equation and exponential strip growth for their ordinary and reflected integrals. -/
def RealOrdinaryBlockNormalizedGrowthStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement →
    (∀ (r t : ℕ) (h : t < r), RealLocalUnequalGrowthAtRanks r t h) ∧
    ∀ r : ℕ, RealLocalEqualGrowthAtRank r

set_option maxHeartbeats 1200000 in
theorem realOrdinaryBlockNormalizedGrowth : RealOrdinaryBlockNormalizedGrowthStatement := by
  intro hO
  constructor
  · intro r t h ds es hd he a D W V hW hV
    have hW' := uniformModel_le_ascendingExpand r ds hd a hW
    have hV' := uniformModel_le_ascendingExpand t es he (-a) hV
    have hA := realLocalUnequalCharacterGrowth r t h (ascendingExpand ds) (ascendingExpand es)
      ⟨_, rfl⟩ ⟨_, rfl⟩ ((realRank_ascendingExpand ds).trans hd)
      ((realRank_ascendingExpand es).trans he) a D W V hW' hV'
    rw [determinant_ascendingExpand, determinant_ascendingExpand] at hA
    have hW₀ : W ∈ realWhittakerModel r ds a := (realWhittakerModels_eq r ds hd a).symm ▸ hW
    have hV₀ : V ∈ realWhittakerModel t es (-a) := (realWhittakerModels_eq t es he (-a)).symm ▸ hV
    obtain ⟨N⟩ := hO.1 r t h ds es hd he a D (⟨W, hW₀⟩, ⟨V, hV₀⟩)
    exact normalizedGrowth_of_ascending hA N
  · intro r ds es hd he a D W V Φ hW hV
    have hW' := uniformModel_le_ascendingExpand r ds hd a hW
    have hV' := uniformModel_le_ascendingExpand r es he (-a) hV
    have hA := realLocalEqualCharacterGrowth_of_canonicalPremises
      RealUniformCanonicalRange.realUniformCanonicalRangePremise
      RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise r
      (ascendingExpand ds) (ascendingExpand es) ⟨_, rfl⟩ ⟨_, rfl⟩
      ((realRank_ascendingExpand ds).trans hd) ((realRank_ascendingExpand es).trans he) a D W V Φ hW' hV'
    rw [determinant_ascendingExpand] at hA
    have hW₀ : W ∈ realWhittakerModel r ds a := (realWhittakerModels_eq r ds hd a).symm ▸ hW
    have hV₀ : V ∈ realWhittakerModel r es (-a) := (realWhittakerModels_eq r es he (-a)).symm ▸ hV
    obtain ⟨N⟩ := hO.2 r ds es hd he a D (⟨W, hW₀⟩, ⟨V, hV₀⟩, Φ)
    exact normalizedGrowth_of_ascending hA N

end Langlands.Global.RankinSelbergGlobal.RealJacquet
