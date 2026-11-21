import Langlands.HarmonicAnalysis.Distribution.OrbitIntegratedDistribution
import Langlands.HarmonicAnalysis.Distribution.OrbitJetLocalLimit

/-! # Covariance of the leading coefficient after orbit integration -/

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

variable {O Z N F : Type*}
  [NormedAddCommGroup O] [NormedSpace ℝ O]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Q : Opens O} {U : Opens Z} {V : Opens N}

local notation "Coord" => ((O × Z) × N)
local notation "Domain" => productTestDomain (productTestDomain Q U) V
local notation "Slice" => productTestDomain U V
local notation "Jet[" i "]" => (N [×i]→L[ℝ] ℝ)

/-- A covariance law on tests supported in the target of a local chart action. -/
def HasLocalWeightedTestCovariance (T : 𝓓'(Domain, F)) (Ψ : OpenPartialHomeomorph Coord Coord)
    (w : Coord → ℝ) (c : ℝ) : Prop :=
  ∀ g : 𝓓(Domain, ℝ), tsupport g ⊆ Ψ.target →
    ∃ f : 𝓓(Domain, ℝ), tsupport f ⊆ Ψ.source ∧
      EqOn f (fun x => w x • g (Ψ x)) Ψ.source ∧ T f = c • T g

omit [NormedSpace ℝ O] [NormedSpace ℝ Z] [NormedSpace ℝ N] in
private theorem exists_openOrbitNormalWindows {K : Set Z} (hK : IsCompact K) {s : Set Coord}
    (hs : IsOpen s) (h : ∀ z ∈ K, ((0, z), 0) ∈ s) (hQ : (0 : O) ∈ Q) (hV : (0 : N) ∈ V) :
    ∃ (Q' : Opens O) (V' : Opens N), (0 : O) ∈ Q' ∧ (0 : N) ∈ V' ∧ Q' ≤ Q ∧ V' ≤ V ∧
      ∀ z ∈ K, ∀ t ∈ Q', ∀ y ∈ V', ((t, z), y) ∈ s := by
  let j (p : Z × (O × N)) : Coord := ((p.2.1, p.1), p.2.2)
  have hj : Continuous j := (continuous_snd.fst.prodMk continuous_fst).prodMk continuous_snd.snd
  have hprod : K ×ˢ ({(0, 0)} : Set (O × N)) ⊆ j ⁻¹' s := by
    rintro ⟨z, p⟩ ⟨hz, hp⟩
    change p ∈ ({(0, 0)} : Set (O × N)) at hp
    rw [mem_singleton_iff] at hp
    subst p
    exact h z hz
  obtain ⟨u, v, _, hv, hu, hzero, huv⟩ := generalized_tube_lemma hK
    (isCompact_singleton (x := ((0 : O), (0 : N)))) (hs.preimage hj) hprod
  obtain ⟨q, n, hqo, hq, hno, hn, hqn⟩ := mem_nhds_prod_iff'.mp (hv.mem_nhds (hzero (mem_singleton _)))
  refine ⟨Q ⊓ ⟨q, hqo⟩, V ⊓ ⟨n, hno⟩, ⟨hQ, hq⟩, ⟨hV, hn⟩, inf_le_left, inf_le_left, ?_⟩
  intro z hz t ht y hy
  change (z, (t, y)) ∈ j ⁻¹' s
  exact huv ⟨hu hz, hqn ⟨ht.2, hy.2⟩⟩

private theorem transverseJet_eq_zero_of_notMem_tsupport (f : 𝓓(Domain, ℝ)) (i : ℕ)
    (p : O × Z) (hp : (p, 0) ∉ tsupport f) (v : Fin i → N) :
    transverseProductJetCLM i f p v = 0 := by
  have h : (f : Coord → ℝ) =ᶠ[𝓝 (p, 0)] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hp] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  rw [transverseProductJetCLM_apply, (h.iteratedFDeriv ℝ i).eq_of_nhds]
  simp

private theorem transverseJet_weighted_pullback {Ψ : OpenPartialHomeomorph Coord Coord}
    (hs : ContDiffOn ℝ ∞ Ψ Ψ.source) (hΨ : PreservesZeroNormalFibers Ψ)
    {w : Coord → ℝ} (hw : ContDiffOn ℝ ∞ w Ψ.source) {f g : 𝓓(Domain, ℝ)}
    (hfg : EqOn f (fun x => w x • g (Ψ x)) Ψ.source) (i : ℕ)
    (hg : ∀ j < i, transverseProductJetCLM j g = 0) (t : O) (z : Z)
    (h : ((t, z), 0) ∈ Ψ.source) (v : Fin i → N) :
    transverseProductJetCLM i f (t, z) v = w ((t, z), 0) •
      transverseProductJetCLM i g ((Ψ ((t, z), 0)).1.1, z)
        (fun k => productNormalDerivative Ψ (t, z) (v k)) := by
  have hf : (f : Coord → ℝ) =ᶠ[𝓝 ((t, z), 0)] fun x => w x • g (Ψ x) := by
    filter_upwards [Ψ.open_source.mem_nhds h] with x hx
    exact hfg hx
  rw [transverseProductJetCLM_apply, (hf.iteratedFDeriv ℝ i).eq_of_nhds]
  exact weighted_transverseProductJet_comp_of_lower_eq_zero g Ψ.open_source hw hs h
    (hΨ (t, z) h) i hg v

variable [FiniteDimensional ℝ O] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ N]
  [MeasurableSpace O] [BorelSpace O] (μ : Measure O) [μ.IsAddHaarMeasure]

/-- Orbit integration transports the signed covariance of ordinary weighted
chart tests to the leading transverse coefficient at zero orbit coordinate. -/
theorem orbitSliceCoefficient_eq_of_localWeightedTestCovariance
    (T : 𝓓'(Domain, F)) (χ : 𝓓(Q, ℝ)) (hχ : (∫ t, χ t ∂μ) = 1)
    (hFactor : ∀ f : 𝓓(Domain, ℝ), T f = orbitSliceDistribution T χ (orbitIntegratedTest μ f))
    (hQ : (0 : O) ∈ Q) (hV : (0 : N) ∈ V)
    {Ψ : OpenPartialHomeomorph Coord Coord} (hs : ContDiffOn ℝ ∞ Ψ Ψ.source)
    (hi : ContDiffOn ℝ ∞ Ψ.symm Ψ.target)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm)
    {w : Coord → ℝ} (hw : ContDiffOn ℝ ∞ w Ψ.source) (c : ℝ)
    (hCov : HasLocalWeightedTestCovariance T Ψ w c)
    (i : ℕ) (hord : HasTransverseJetOrder (orbitSliceDistribution T χ) i)
    (ζ : 𝓓(V, ℝ)) (hζ : (ζ : N → ℝ) =ᶠ[𝓝 0] 1)
    (a b : 𝓓(U, Jet[i])) (ha : ∀ z v (σ : Equiv.Perm (Fin i)), a z (v ∘ σ) = a z v)
    (hTarget : ∀ z ∈ tsupport a, ((0, z), 0) ∈ Ψ.target)
    (hb : ∀ z, b z = orbitJetTransportKernel Ψ w i (z, 0) (a z)) :
    transverseProductJetCoefficient (orbitSliceDistribution T χ) ζ i b =
      c • transverseProductJetCoefficient (orbitSliceDistribution T χ) ζ i a := by
  let S := orbitSliceDistribution T χ
  let C := transverseProductJetCoefficient S ζ i
  obtain ⟨B, hB0, hB⟩ := exists_orbitJetTransportFamily μ hs hi hΨ hΨi hw i a hTarget χ hχ
  have hB0b : B 0 = b := TestFunction.ext (fun z => (hB0 z).trans (hb z).symm)
  obtain ⟨Q', V', h0Q', h0V', hQQ', hVV', htarget⟩ :=
    exists_openOrbitNormalWindows a.hasCompactSupport Ψ.open_target hTarget hQ hV
  obtain ⟨η', hη'⟩ := exists_test_eq_one_near_zero h0V'
  let η : 𝓓(V, ℝ) := TestFunction.monoCLM ℝ η'
  have hηeq : (η : N → ℝ) = η' := by simp [η, hVV']
  have hη : (η : N → ℝ) =ᶠ[𝓝 0] 1 := hηeq ▸ hη'
  let p := productJetExtensionCLM η i a
  have hlow (j : ℕ) (hj : j < i) : transverseProductJetCLM j p = 0 :=
    transverseProductJetCLM_productJetExtensionCLM_of_ne η hη hj.ne' a
  have htop : transverseProductJetCLM i p = a :=
    transverseProductJetCLM_productJetExtensionCLM_self η hη i a ha
  have hSp : S p = C a := by
    change S p = transverseProductJetCoefficient S ζ i a
    rw [eval_eq_transverseProductJetCoefficient_of_lower_eq_zero S i hord ζ hζ p hlow, htop]
  have heq : (fun ε : ℝ => C (B ε)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => c • C a) := by
    filter_upwards [hB.filter_mono nhdsWithin_le_nhds,
      (eventually_dilatedOrbitTest_support_subset χ h0Q').filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hBε hε hpos
    let χ' := dilatedOrbitTest χ hpos hε
    let δ : 𝓓(Q, ℝ) := TestFunction.monoCLM ℝ χ'
    have hδ : (δ : O → ℝ) = χ' := by simp [δ, hQQ']
    have hδone : (∫ t, δ t ∂μ) = 1 := by
      simpa [hδ, χ', smul_eq_mul, hχ] using integral_dilatedOrbitTest_smul μ χ hpos hε (fun _ => (1 : ℝ))
    let g := orbitProductTestCLM δ p
    have hgt : tsupport g ⊆ Ψ.target := by
      rintro ⟨⟨t, z⟩, y⟩ hx
      obtain ⟨ht, hzy⟩ := tsupport_orbitProductTestCLM_subset δ p hx
      obtain ⟨hz, hy⟩ := tsupport_productJetExtensionCLM_subset η i a hzy
      exact htarget z hz t (χ'.tsupport_subset (hδ ▸ ht)) y (η'.tsupport_subset (hηeq ▸ hy))
    obtain ⟨f, hf, hfg, hTf⟩ := hCov g hgt
    have hg_low (j : ℕ) (hj : j < i) : transverseProductJetCLM j g = 0 := by
      ext ⟨t, z⟩ v
      change transverseProductJetCLM j (orbitProductTestCLM δ p) (t, z) v = 0
      rw [transverseProductJetCLM_orbitProductTestCLM δ p j t z v, hlow j hj]
      simp
    have hf_low (j : ℕ) (hj : j < i) : transverseProductJetCLM j f = 0 := by
      ext ⟨t, z⟩ v
      change transverseProductJetCLM j f (t, z) v = 0
      by_cases hx : ((t, z), 0) ∈ Ψ.source
      · rw [transverseJet_weighted_pullback hs hΨ hw hfg j (fun k hk => hg_low k (hk.trans hj)) t z hx v,
          hg_low j hj]
        simp
      · exact transverseJet_eq_zero_of_notMem_tsupport f j (t, z) (fun h => hx (hf h)) v
    have hI_low (j : ℕ) (hj : j < i) : transverseProductJetCLM j (orbitIntegratedTest μ f) = 0 := by
      ext z v
      change transverseProductJetCLM j (orbitIntegratedTest μ f) z v = 0
      rw [transverseProductJetCLM_orbitIntegratedTest, hf_low j hj]
      simp
    have hI_top : transverseProductJetCLM i (orbitIntegratedTest μ f) = B ε := by
      apply TestFunction.ext
      intro z
      rw [transverseProductJetCLM_orbitIntegratedTest_form, hBε hpos z]
      let e := zeroNormalOrbitChart Ψ hΨ hΨi z
      have hout (t : O) (ht : t ∉ e.source) : transverseProductJetCLM i f (t, z) = 0 := by
        ext v
        exact transverseJet_eq_zero_of_notMem_tsupport f i (t, z) (fun h => ht (hf h)) v
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro t ht
      ext v
      rw [transverseJet_weighted_pullback hs hΨ hw hfg i hg_low t z ht v]
      change w ((t, z), 0) • transverseProductJetCLM i (orbitProductTestCLM δ p)
        (e t, z) (fun k => productNormalDerivative Ψ (t, z) (v k)) = _
      rw [transverseProductJetCLM_orbitProductTestCLM, htop]
      simp only [hδ, χ', dilatedOrbitTest_apply, smul_smul, smul_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      rw [mul_comm (w ((t, z), 0))]
    have hTf' : T f = C (B ε) := by
      rw [hFactor f, eval_eq_transverseProductJetCoefficient_of_lower_eq_zero S i hord ζ hζ _ hI_low, hI_top]
    have hTg : T g = C a := by
      rw [hFactor g, orbitIntegratedTest_orbitProductTestCLM μ δ hδone p]
      exact hSp
    exact hTf'.symm.trans (hTf.trans (congrArg (c • ·) hTg))
  have ht : Tendsto (fun ε : ℝ => C (B ε)) (𝓝[>] (0 : ℝ)) (𝓝 (C (B 0))) :=
    (C.continuous.comp B.continuous).continuousAt.continuousWithinAt
  have h := tendsto_nhds_unique_of_eventuallyEq ht tendsto_const_nhds heq
  rwa [hB0b] at h

end Langlands.HarmonicAnalysis
