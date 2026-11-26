import Langlands.HarmonicAnalysis.MeasureDensityTransport
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # A Haar density in additive unit coordinates -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory MeasureTheory.Measure Set Function
open scoped ENNReal NNReal Pointwise Topology

private theorem unitCoordinateImage_mul_left {A : Type*} [Ring A] (g : Aˣ) (B : Set Aˣ) :
    Units.val '' ((g * ·) ⁻¹' B) = g⁻¹ • (Units.val '' B) := by
  ext a
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact Set.mem_smul_set.mpr ⟨(g * h).val, ⟨g * h, hh, rfl⟩, by
      change (g⁻¹ : Aˣ).val * (g.val * h.val) = h.val
      simp⟩
  · intro ha
    obtain ⟨_, ⟨h, hh, rfl⟩, rfl⟩ := Set.mem_smul_set.mp ha
    exact ⟨g⁻¹ * h, by change g * (g⁻¹ * h) ∈ B; simpa using hh, rfl⟩

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
  [TotallyDisconnectedSpace Aˣ] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ]

/-- On the open unit locus the inverse left-multiplication modulus is a locally
constant weight converting additive Haar in unit coordinates to group Haar. -/
def UnitHaarDensityStatement (μ : Measure A) : Prop :=
  ∃ w : LocallyConstant Aˣ ℝ≥0, (∀ g, 0 < w g) ∧
    (∀ g, (w g : ℝ≥0∞) = (distribHaarChar A g : ℝ≥0∞)⁻¹) ∧
    ((μ.comap Units.val).withDensity (fun g => (w g : ℝ≥0∞))).IsHaarMeasure

/-- The weighted measure is Haar because the left-translation scale of additive
Haar is canceled by the inverse modulus in the weight. -/
theorem unitHaarDensity (hval : _root_.Topology.IsOpenEmbedding (Units.val : Aˣ → A))
    (μ : Measure A) [μ.IsAddHaarMeasure] : UnitHaarDensityStatement μ := by
  classical
  let δ : Aˣ →* ℝ≥0 := distribHaarChar A
  let r := μ.comap (Units.val : Aˣ → A)
  have hj := hval.measurableEmbedding
  have : LocallyCompactSpace Aˣ := hval.locallyCompactSpace
  have : T2Space Aˣ := hval.isEmbedding.t2Space
  have : SecondCountableTopology Aˣ := hval.isEmbedding.secondCountableTopology
  let _ : Measure.Regular μ := inferInstance
  obtain ⟨K, _, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance Aˣ ∅ ⊤
  let C := (Units.val : Aˣ → A) '' (K : Set Aˣ)
  have hCo : IsOpen C := hval.isOpenMap (K : Set Aˣ) K.isOpen
  have hCc : IsCompact C := hK.image hval.continuous
  have hC0 : μ C ≠ 0 := hCo.measure_ne_zero μ ⟨1, 1, K.one_mem, rfl⟩
  have hKδ (g : Aˣ) (hg : g ∈ K) : δ g = 1 := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hC0 hCc.measure_ne_top
    have hC : g • C = C := by
      rw [← inv_inv g, ← unitCoordinateImage_mul_left]
      congr 1
      ext a
      change g⁻¹ * a ∈ K ↔ a ∈ K
      exact ⟨fun h => by simpa using K.mul_mem hg h, K.mul_mem (K.inv_mem hg)⟩
    rw [hC, ENNReal.coe_one, one_mul]
  have hδ : IsLocallyConstant δ := by
    apply (IsLocallyConstant.iff_eventually_eq δ).2
    intro g
    filter_upwards [(K.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds
      (show g⁻¹ * g ∈ K by simp)] with x hx
    have hk : δ (g⁻¹ * x) = 1 := hKδ _ hx
    calc
      δ x = δ (g * (g⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = δ g := by rw [map_mul, hk, mul_one]
  let w : LocallyConstant Aˣ ℝ≥0 := ⟨fun g => δ g⁻¹, hδ.comp_continuous continuous_inv⟩
  have hwp (g : Aˣ) : 0 < w g := distribHaarChar_pos
  let η := r.withDensity (fun g => (w g : ℝ≥0∞))
  refine ⟨w, hwp, fun g => ?_, ?_⟩
  · change (δ g⁻¹ : ℝ≥0∞) = (δ g : ℝ≥0∞)⁻¹
    have h0 : (δ g : ℝ≥0∞) ≠ 0 := by exact_mod_cast (distribHaarChar_pos (A := A) (g := g)).ne'
    have hmul : (δ g : ℝ≥0∞) * (δ g⁻¹ : ℝ≥0∞) = 1 := by
      rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one]
    calc
      _ = (δ g : ℝ≥0∞)⁻¹ * ((δ g : ℝ≥0∞) * (δ g⁻¹ : ℝ≥0∞)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ENNReal.coe_ne_top, one_mul]
      _ = _ := by rw [hmul, mul_one]
  · let _ : IsFiniteMeasureOnCompacts r := IsFiniteMeasureOnCompacts.comap' μ hval.continuous hj
    let _ : IsOpenPosMeasure r := IsOpenPosMeasure.comap μ hval
    let _ : IsLocallyFiniteMeasure η := IsLocallyFiniteMeasure.withDensity_coe w.continuous
    have hleft (g : Aˣ) : η.map (g * ·) = η := by
      have hmap : r.map (g * ·) = δ g⁻¹ • r := by
        ext B hB
        change Measure.map (g * ·) (μ.comap Units.val) B =
          (δ g⁻¹ • μ.comap Units.val) B
        rw [Measure.map_apply (measurable_const_mul g) hB, Measure.smul_apply,
          hj.comap_apply, hj.comap_apply, unitCoordinateImage_mul_left]
        exact (distribHaarChar_mul μ g⁻¹ _).symm
      let e := (Homeomorph.mulLeft g).toMeasurableEquiv
      change (r.withDensity _).map e = _
      rw [Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_equiv]
      change ((r.map (g * ·)).withDensity fun x => (w (g⁻¹ * x) : ℝ≥0∞)) = η
      have hw : Measurable fun x : Aˣ => (w (g⁻¹ * x) : ℝ≥0∞) :=
        w.continuous.measurable.coe_nnreal_ennreal.comp (measurable_const_mul g⁻¹)
      rw [hmap, ← Measure.coe_nnreal_smul, withDensity_smul_measure, ← withDensity_smul _ hw]
      congr 1
      funext x
      change (δ g⁻¹ : ℝ≥0∞) * (δ (g⁻¹ * x)⁻¹ : ℝ≥0∞) = (δ x⁻¹ : ℝ≥0∞)
      rw [mul_inv_rev, inv_inv, map_mul, ← ENNReal.coe_mul]
      apply congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
      calc
        _ = δ x⁻¹ * (δ g⁻¹ * δ g) := mul_left_comm _ _ _
        _ = _ := by rw [← map_mul, inv_mul_cancel, map_one, mul_one]
    have hac : r ≪ η := withDensity_absolutelyContinuous'
      w.continuous.measurable.coe_nnreal_ennreal.aemeasurable (Filter.Eventually.of_forall fun g => by
        exact_mod_cast (hwp g).ne')
    exact { toIsMulLeftInvariant := ⟨hleft⟩
            toIsFiniteMeasureOnCompacts := inferInstance
            toIsOpenPosMeasure := ⟨fun B hB hn => by
              by_contra! hs
              exact hB.measure_ne_zero r hn (hac hs)⟩ }

end Langlands.HarmonicAnalysis.UnitConjugation
