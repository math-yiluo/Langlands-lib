import Langlands.HarmonicAnalysis.Distribution.SmoothTestParameters
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Smooth test families obtained by shrinking a normalized orbit test -/

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E O F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup O] [NormedSpace ℝ O]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Opens E} {Q Q' : Opens O}

/-- Scale an orbit test by a positive dilation and divide by the volume factor. -/
def dilatedOrbitTest (χ : 𝓓(Q, ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hQ : (fun t : O => ε • t) '' tsupport χ ⊆ Q') : 𝓓(Q', ℝ) := by
  let g (t : O) := (ε ^ Module.finrank ℝ O)⁻¹ * χ (ε⁻¹ • t)
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul (χ.contDiff.comp (contDiff_id.const_smul _))
  have hK := χ.hasCompactSupport.image (continuous_const_smul (ε : ℝ))
  have hs : support g ⊆ (fun t : O => ε • t) '' tsupport χ := by
    intro t ht
    refine ⟨ε⁻¹ • t, subset_tsupport _ ?_, smul_inv_smul₀ hε.ne' t⟩
    intro h
    exact ht (by simp [g, show χ (ε⁻¹ • t) = 0 from h])
  exact ⟨g, hg, HasCompactSupport.of_support_subset_isCompact hK hs,
    (closure_minimal hs hK.isClosed).trans hQ⟩

@[simp]
theorem dilatedOrbitTest_apply (χ : 𝓓(Q, ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hQ : (fun t : O => ε • t) '' tsupport χ ⊆ Q') (t : O) :
    dilatedOrbitTest χ hε hQ t = (ε ^ Module.finrank ℝ O)⁻¹ * χ (ε⁻¹ • t) := rfl

/-- A test supported in a compact set dilates into every neighborhood of the origin. -/
theorem eventually_dilatedOrbitTest_support_subset (χ : 𝓓(Q, ℝ)) (hQ' : 0 ∈ Q') :
    ∀ᶠ ε : ℝ in 𝓝 0, (fun t : O => ε • t) '' tsupport χ ⊆ Q' := by
  obtain ⟨r, hr, hrQ⟩ := Metric.isOpen_iff.mp Q'.isOpen 0 hQ'
  obtain ⟨C, hC⟩ := χ.hasCompactSupport.isBounded.exists_norm_le
  let R := max C 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hr hR)] with ε hε
  rintro _ ⟨t, ht, rfl⟩
  apply hrQ
  rw [Metric.mem_ball, dist_zero_right, norm_smul]
  rw [Metric.mem_ball, dist_zero_right] at hε
  exact ((mul_le_mul_of_nonneg_left ((hC t ht).trans (le_max_left _ _)) (norm_nonneg ε)).trans_lt
    ((lt_div_iff₀ hR).mp hε))

/-- The volume factor cancels under the change of variables by the dilation. -/
theorem integral_dilatedOrbitTest_smul [FiniteDimensional ℝ O] [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) [μ.IsAddHaarMeasure]
    (χ : 𝓓(Q, ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hQ : (fun t : O => ε • t) '' tsupport χ ⊆ Q') (g : O → G) :
    (∫ t, dilatedOrbitTest χ hε hQ t • g t ∂μ) = ∫ t, χ t • g (ε • t) ∂μ := by
  let a := ε ^ Module.finrank ℝ O
  let k (t : O) := χ t • g (ε • t)
  have heq (t : O) : dilatedOrbitTest χ hε hQ t • g t = a⁻¹ • k (ε⁻¹ • t) := by
    simp only [dilatedOrbitTest_apply, k, smul_inv_smul₀ hε.ne', smul_smul, a]
  simp_rw [heq]
  rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg μ k hε.le]
  change a⁻¹ • (a • ∫ t, k t ∂μ) = _
  rw [inv_smul_smul₀ (pow_ne_zero _ hε.ne')]

section Average

variable [MeasurableSpace O] [BorelSpace O] (μ : Measure O) [IsLocallyFiniteMeasure μ]

private theorem contDiff_orbitAverage (χ : 𝓓(Q, ℝ))
    {H : E × O → F →L[ℝ] G} (hH : ContDiff ℝ ∞ H) (f : 𝓓(U, F)) :
    ContDiff ℝ ∞ (fun p : ℝ × E => ∫ t, χ t • H (p.2, p.1 • t) (f p.2) ∂μ) := by
  let K := tsupport χ
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp χ.hasCompactSupport
  let ν : Measure K := μ.comap Subtype.val
  have hK : MeasurableSet K := χ.hasCompactSupport.isClosed.measurableSet
  let _ : IsFiniteMeasure ν := ⟨by
    change μ.comap (Subtype.val : K → O) univ < ⊤
    rw [Measure.comap_apply _ Subtype.val_injective
      (fun s hs => (MeasurableEmbedding.subtype_coe hK).measurableSet_image' hs) _ MeasurableSet.univ,
      image_univ, Subtype.range_coe]
    exact χ.hasCompactSupport.measure_lt_top⟩
  let j : C(K, O) := ⟨Subtype.val, continuous_subtype_val⟩
  let h (p : (ℝ × E) × O) : G := χ p.2 • H (p.1.2, p.1.1 • p.2) (f p.1.2)
  have hh : ContDiff ℝ ∞ h :=
    (χ.contDiff.comp contDiff_snd).smul
      ((hH.comp (contDiff_fst.snd.prodMk (contDiff_fst.fst.smul contDiff_snd))).clm_apply
        (f.contDiff.comp contDiff_fst.snd))
  let A (p : ℝ × E) : C(K, G) :=
    ⟨fun t => h (p, t.val), hh.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hA : ContDiff ℝ ∞ A := by
    apply contDiffOn_univ.mp
    exact Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint (f := A) j
      isOpen_univ isOpen_univ (fun _ => mem_univ _) hh.contDiffOn (fun _ _ _ => rfl)
  have heq : (fun p : ℝ × E => ∫ t, h (p, t) ∂μ) =
      Langlands.Analysis.compactContinuousIntegralCLM ν ∘ A := by
    funext p
    rw [Function.comp_apply, Langlands.Analysis.compactContinuousIntegralCLM_apply]
    convert (setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun t => h (p, t))
      (s := K) (μ := μ) ?_).symm using 1
    · exact integral_subtype_comap hK (fun t => h (p, t))
    · intro t ht
      simp [h, image_eq_zero_of_notMem_tsupport ht]
  change ContDiff ℝ ∞ (fun p : ℝ × E => ∫ t, h (p, t) ∂μ)
  rw [heq]
  exact (Langlands.Analysis.compactContinuousIntegralCLM ν).contDiff.comp hA

/-- Averaging a smooth operator-valued kernel against a fixed orbit test with
argument `ε • t` gives a continuous parameter family in the smooth test topology. -/
def smoothOrbitAverageFamily (χ : 𝓓(Q, ℝ)) {H : E × O → F →L[ℝ] G}
    (hH : ContDiff ℝ ∞ H) (f : 𝓓(U, F)) : C(ℝ, 𝓓(U, G)) := by
  let K : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
  let h (p : ℝ × E) : G := ∫ t, χ t • H (p.2, p.1 • t) (f p.2) ∂μ
  have hh : ContDiff ℝ ∞ h := contDiff_orbitAverage μ χ hH f
  have hs : ∀ ε ∈ (univ : Set ℝ), ∀ x ∉ K, h (ε, x) = 0 := by
    intro ε _ x hx
    simp [h, image_eq_zero_of_notMem_tsupport (f := f) hx]
  let B := compactTestFamily hh hs
  exact ⟨fun ε => TestFunction.ofSupportedIn f.tsupport_subset (B ⟨ε, mem_univ _⟩),
    (TestFunction.continuous_ofSupportedIn f.tsupport_subset).comp
      ((continuous_compactTestFamily hh hs).comp (continuous_id.subtype_mk fun _ => mem_univ _))⟩

@[simp]
theorem smoothOrbitAverageFamily_apply (χ : 𝓓(Q, ℝ))
    {H : E × O → F →L[ℝ] G} (hH : ContDiff ℝ ∞ H) (f : 𝓓(U, F)) (ε : ℝ) (z : E) :
    smoothOrbitAverageFamily μ χ hH f ε z = ∫ t, χ t • H (z, ε • t) (f z) ∂μ := rfl

@[simp]
theorem smoothOrbitAverageFamily_zero_apply [CompleteSpace G] (χ : 𝓓(Q, ℝ))
    (hχ : (∫ t, χ t ∂μ) = 1) {H : E × O → F →L[ℝ] G}
    (hH : ContDiff ℝ ∞ H) (f : 𝓓(U, F)) (z : E) :
    smoothOrbitAverageFamily μ χ hH f 0 z = H (z, 0) (f z) := by
  simp [smoothOrbitAverageFamily_apply, integral_smul_const, hχ]

end Average

end Langlands.HarmonicAnalysis
