import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Additive Haar null sets and Haar measure on units -/

namespace Langlands.Analysis

open MeasureTheory Set

/-- An additive Haar null set pulls back to a multiplicative Haar null set on
units, provided the units form an open subset of the ring. -/
theorem measure_preimage_unitsVal_eq_zero {R : Type*} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R]
    [SecondCountableTopology Rˣ] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (ν : Measure R) [ν.IsAddHaarMeasure] (μ : Measure Rˣ) [μ.IsHaarMeasure]
    [SigmaFinite μ] (hopen : IsOpen (range (Units.val : Rˣ → R)))
    {Z : Set R} (hZ : MeasurableSet Z) (hzero : ν Z = 0) :
    μ ((Units.val : Rˣ → R) ⁻¹' Z) = 0 := by
  classical
  have hm : MeasurableSet {p : R × Rˣ | p.1 * (p.2 : R) ∉ Z} :=
    (continuous_fst.mul (Units.continuous_val.comp continuous_snd)).measurable hZ.compl
  have hsection (g : Rˣ) : ∀ᵐ a ∂ν, a * (g : R) ∉ Z := by
    let e : R ≃+ R := { toEquiv := g.mulRight, map_add' := fun a b => add_mul a b g }
    have hc : Continuous e := continuous_id.mul continuous_const
    have hc' : Continuous e.symm := continuous_id.mul continuous_const
    have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν hc hc'
    have hnull : (ν.map e) Z = 0 :=
      Measure.absolutelyContinuous_isAddHaarMeasure (ν.map e) ν hzero
    rw [Measure.map_apply hc.measurable hZ] at hnull
    apply ae_iff.mpr
    have hpreimage : ν {a : R | a * (g : R) ∈ Z} = 0 := hnull
    simpa only [not_not] using hpreimage
  have hae : ∀ᵐ a ∂ν, ∀ᵐ (g : Rˣ) ∂μ, a * (g : R) ∉ Z :=
    (Measure.ae_ae_comm hm).mpr (Filter.Eventually.of_forall hsection)
  have hpos : ν (range (Units.val : Rˣ → R)) ≠ 0 :=
    (hopen.measure_pos ν (range_nonempty _)).ne'
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (hae.filter_mono (ae_mono Measure.restrict_le_self))
  have htranslated : μ ((g * ·) ⁻¹' ((Units.val : Rˣ → R) ⁻¹' Z)) = 0 := by
    simpa only [mem_ofPred_eq, not_not, preimage, Units.val_mul] using ae_iff.mp hg
  rwa [measure_preimage_mul] at htranslated

end Langlands.Analysis
