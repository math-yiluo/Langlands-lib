import Langlands.HarmonicAnalysis.Distribution.OrbitJetChangeOfVariables
import Langlands.HarmonicAnalysis.Distribution.SmoothOrbitJetLimit
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # The limit of transported shrinking orbit averages -/

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

section LocalKernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_contDiff_extension_on_compact {G : E → F} {s K : Set E}
    (hs : IsOpen s) (hG : ContDiffOn ℝ ∞ G s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ H : E → F, ContDiff ℝ ∞ H ∧ EqOn H G K := by
  obtain ⟨u, hu, hKu, hus⟩ := normal_exists_closure_subset hK.isClosed hs hKs
  obtain ⟨b, hb, _, hbu, hbK⟩ := exists_contDiff_support_eq_eq_one_iff hu hK.isClosed hKu
    (n := (⊤ : ℕ∞))
  refine ⟨fun x => b x • G x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ s
    · exact hb.contDiffAt.smul (hG.contDiffAt (hs.mem_nhds hx))
    · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (show x ∈ (closure u)ᶜ from
        fun hx' => hx (hus hx'))] with y hy
      rw [notMem_support.mp (show y ∉ support b from fun hy' => hy (subset_closure (hbu ▸ hy'))),
        zero_smul]
  · intro x hx
    change b x • G x = G x
    rw [(hbK x).mp hx, one_smul]

end LocalKernel

variable {Z O F G : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup O] [NormedSpace ℝ O] [FiniteDimensional ℝ O]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace O] [BorelSpace O] (μ : Measure O)
  {U : Opens Z} {Q : Opens O}

section Average

variable [IsLocallyFiniteMeasure μ]
  {H : Z × O → F →L[ℝ] G} {s K : Set (Z × O)}
  (hs : IsOpen s) (hH : ContDiffOn ℝ ∞ H s) (hK : IsCompact K) (hKs : K ⊆ s)

/-- A continuous family of orbit averages from a smooth extension of a local
kernel on a compact set. -/
def smoothOrbitAverageFamilyOn (χ : 𝓓(Q, ℝ)) (f : 𝓓(U, F)) : C(ℝ, 𝓓(U, G)) :=
  smoothOrbitAverageFamily μ χ (exists_contDiff_extension_on_compact hs hH hK hKs).choose_spec.1 f

/-- When the evaluation points lie in the compact set wherever both tests contribute,
the family agrees with the average of the supplied local kernel. -/
theorem smoothOrbitAverageFamilyOn_apply (χ : 𝓓(Q, ℝ)) (f : 𝓓(U, F)) (ε : ℝ)
    (hε : ∀ z ∈ tsupport f, ∀ t ∈ tsupport χ, (z, ε • t) ∈ K) (z : Z) :
    smoothOrbitAverageFamilyOn μ hs hH hK hKs χ f ε z = ∫ t, χ t • H (z, ε • t) (f z) ∂μ := by
  unfold smoothOrbitAverageFamilyOn
  rw [smoothOrbitAverageFamily_apply]
  congr 1
  funext t
  by_cases hz : z ∈ tsupport f
  · by_cases ht : t ∈ tsupport χ
    · rw [(exists_contDiff_extension_on_compact hs hH hK hKs).choose_spec.2 (hε z hz t ht)]
    · simp [image_eq_zero_of_notMem_tsupport ht]
  · simp [image_eq_zero_of_notMem_tsupport hz]

theorem smoothOrbitAverageFamilyOn_zero_apply [CompleteSpace G] (χ : 𝓓(Q, ℝ))
    (hχ : (∫ t, χ t ∂μ) = 1) (f : 𝓓(U, F)) (hf : ∀ z ∈ tsupport f, (z, (0 : O)) ∈ K)
    (z : Z) : smoothOrbitAverageFamilyOn μ hs hH hK hKs χ f 0 z = H (z, 0) (f z) := by
  rw [smoothOrbitAverageFamilyOn_apply μ hs hH hK hKs χ f 0 (by simpa using fun z hz _ _ => hf z hz) z]
  simp [integral_smul_const, hχ]

end Average

section Transport

variable [μ.IsAddHaarMeasure]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace F]

local notation "Coord" => ((O × Z) × N)
local notation "Jet[" i "]" => (N [×i]→L[ℝ] F)

/-- Transported shrinking orbit tests extend continuously to zero dilation
in the slice test topology. Their value at zero is the transport kernel at
the zero target orbit coordinate. -/
theorem exists_orbitJetTransportFamily
    {Ψ : OpenPartialHomeomorph Coord Coord} (hs : ContDiffOn ℝ ∞ Ψ Ψ.source)
    (hi : ContDiffOn ℝ ∞ Ψ.symm Ψ.target)
    (hΨ : PreservesZeroNormalFibers Ψ) (hΨi : PreservesZeroNormalFibers Ψ.symm)
    {w : Coord → ℝ} (hw : ContDiffOn ℝ ∞ w Ψ.source) (i : ℕ)
    (a : 𝓓(U, Jet[i])) (ha : ∀ z ∈ tsupport a, ((0, z), 0) ∈ Ψ.target)
    (χ : 𝓓(Q, ℝ)) (hχ : (∫ t, χ t ∂μ) = 1) :
    ∃ B : C(ℝ, 𝓓(U, Jet[i])),
      (∀ z, B 0 z = orbitJetTransportKernel Ψ w i (z, 0) (a z)) ∧
      ∀ᶠ ε : ℝ in 𝓝 0, 0 < ε → ∀ z,
        let e := zeroNormalOrbitChart Ψ hΨ hΨi z
        B ε z = ∫ t in e.source,
          ((ε ^ Module.finrank ℝ O)⁻¹ * χ (ε⁻¹ • e t) * w ((t, z), 0)) •
          (a z).compContinuousLinearMap (fun _ => productNormalDerivative Ψ (t, z)) ∂μ := by
  let s : Set (Z × O) := {p | ((p.2, p.1), 0) ∈ Ψ.target}
  have hso : IsOpen s := Ψ.open_target.preimage ((continuous_snd.prodMk continuous_fst).prodMk continuous_const)
  have hsa : tsupport a ×ˢ ({0} : Set O) ⊆ s := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    rw [mem_singleton_iff] at ht
    change t = 0 at ht
    subst t
    exact ha z hz
  obtain ⟨u, v, _, hv, hau, h0v, huv⟩ := generalized_tube_lemma a.hasCompactSupport
    (isCompact_singleton (x := (0 : O))) hso hsa
  obtain ⟨r, hr, hrv⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hv.mem_nhds (h0v (mem_singleton _)))
  let K := tsupport a ×ˢ Metric.closedBall (0 : O) r
  have hK : IsCompact K := a.hasCompactSupport.prod (isCompact_closedBall _ _)
  have hKs : K ⊆ s := (prod_mono hau hrv).trans huv
  have hH := contDiffOn_orbitJetTransportKernel (F := F) hs hi hΨ hΨi hw i
  let B := smoothOrbitAverageFamilyOn μ hso hH hK hKs χ a
  refine ⟨B, fun z => smoothOrbitAverageFamilyOn_zero_apply μ hso hH hK hKs χ hχ a
    (fun x hx => ⟨hx, Metric.mem_closedBall_self hr.le⟩) z, ?_⟩
  let Qr : Opens O := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  filter_upwards [eventually_dilatedOrbitTest_support_subset (Q' := Qr) χ (Metric.mem_ball_self hr)]
    with ε hε hpos z
  let e := zeroNormalOrbitChart Ψ hΨ hΨi z
  let χr := dilatedOrbitTest χ hpos hε
  let g (t : O) : Jet[i] := orbitJetTransportKernel Ψ w i (z, t) (a z)
  have hεK (x : Z) (hx : x ∈ tsupport a) (t : O) (ht : t ∈ tsupport χ) : (x, ε • t) ∈ K :=
    ⟨hx, Metric.ball_subset_closedBall (hε ⟨t, ht, rfl⟩)⟩
  have hzero (t : O) (ht : t ∉ e.target) : χr t • g t = 0 := by
    by_cases hz : z ∈ tsupport a
    · have ht' : t ∉ Qr := by
        intro h
        have hh : (z, t) ∈ s := hKs ⟨hz, Metric.ball_subset_closedBall h⟩
        exact ht (show ((t, z), 0) ∈ Ψ.target from hh)
      have hχr : χr t = 0 := χr.zero_on_compl ht'
      rw [hχr, zero_smul]
    · simp [g, image_eq_zero_of_notMem_tsupport hz]
  rw [smoothOrbitAverageFamilyOn_apply μ hso hH hK hKs χ a ε hεK z]
  change (∫ t, χ t • g (ε • t) ∂μ) = _
  rw [← integral_dilatedOrbitTest_smul μ χ hpos hε g,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact integral_orbitJetTransportKernel μ hs hi hΨ hΨi w i z χr (a z)

end Transport

end Langlands.HarmonicAnalysis
