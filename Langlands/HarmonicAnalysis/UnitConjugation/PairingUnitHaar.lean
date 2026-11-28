import Langlands.BaseChange.FiniteAlgebraUnits
import Langlands.HarmonicAnalysis.UnitConjugation.PairingHaar
import Langlands.HarmonicAnalysis.UnitConjugation.UnitHaarDensity

/-! # Unimodularity of the unit group from an invariant pairing -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory Set Function _root_.Topology
open scoped ENNReal NNReal

universe u v

/-- The unit group of a finite-dimensional local algebra with an invariant pairing
is unimodular. -/
def PairingUnitHaarUnimodularityStatement.{u', v'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (A : Type v') [Ring A] [Algebra F A] [FiniteDimensional F A] [TopologicalSpace A]
    [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    (B : LinearMap.BilinForm F A) (μ : Measure Aˣ) [μ.IsHaarMeasure],
    IsInvariantPairing B → μ.IsMulRightInvariant

theorem pairingUnitHaarUnimodularity : PairingUnitHaarUnimodularityStatement.{u, v} := by
  intro F _ _ _ _ A _ _ _ _ _ _ _ _ _ B μ _ hB
  have := IsModuleTopology.isTopologicalRing F A
  have : T2Space A := t2Space_of_finiteDimensional F A
  have : LocallyCompactSpace A := locallyCompactSpace_of_finiteDimensional F A
  have : SecondCountableTopology A := secondCountableTopology_of_finiteDimensional F A
  have : CompactOpenExhaustion A := compactOpenExhaustion_of_finiteDimensional F A
  have : TotallySeparatedSpace A := by
    apply totallySeparatedSpace_iff_exists_isClopen.mpr
    intro x y hxy
    have h₀ : (0 : A) ∈ ({y - x} : Set A)ᶜ := by
      simpa only [mem_compl_iff, mem_singleton_iff, eq_comm] using sub_ne_zero.mpr hxy.symm
    obtain ⟨L, hLc, hLo, hL⟩ := CompactOpenExhaustion.exists_subset _
      (isOpen_compl_singleton.mem_nhds h₀)
    let U := (fun a : A => a - x) ⁻¹' (L : Set A)
    have hs : Continuous (fun a : A => a - x) := continuous_id.sub continuous_const
    refine ⟨U, ⟨hLc.isClosed.preimage hs, hLo.preimage hs⟩, ?_, ?_⟩
    · change x - x ∈ L
      rw [sub_self]
      exact L.zero_mem
    · exact fun hy => (hL hy) rfl
  have hval := Langlands.BaseChange.finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := A)
  have : LocallyCompactSpace Aˣ := hval.locallyCompactSpace
  have : SecondCountableTopology Aˣ := hval.isEmbedding.secondCountableTopology
  have : TotallyDisconnectedSpace Aˣ := hval.isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let μA : Measure A := Measure.addHaar
  have : μA.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar : Measure A).IsAddHaarMeasure
  obtain ⟨w, _, hw, hη⟩ := unitHaarDensity hval μA
  let r := μA.comap (Units.val : Aˣ → A)
  let η := r.withDensity fun u => (w u : ℝ≥0∞)
  have : η.IsHaarMeasure := hη
  let C (g : Aˣ) : Aˣ ≃ₜ Aˣ := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  have hConj (g : Aˣ) : η.map (C g) = η := by
    let D := conjugationHomeomorph g
    have hEmb := hval.measurableEmbedding
    have hComp (u : Aˣ) : ((C g u : Aˣ) : A) = D (u : A) := rfl
    have hr : r.map (C g) = r := by
      ext s hs
      rw [Measure.map_apply (C g).continuous.measurable hs]
      change (μA.comap Units.val) ((C g) ⁻¹' s) = (μA.comap Units.val) s
      rw [hEmb.comap_apply, hEmb.comap_apply]
      have himg : Units.val '' ((C g) ⁻¹' s) = D ⁻¹' (Units.val '' s) := by
        ext a
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact ⟨C g u, hu, hComp u⟩
        · rintro ⟨u, hu, he⟩
          refine ⟨(C g).symm u, ?_, ?_⟩
          · change C g ((C g).symm u) ∈ s
            simpa only [(C g).apply_symm_apply] using hu
          · apply D.injective
            rw [← hComp, (C g).apply_symm_apply]
            exact he
      rw [himg]
      exact (pairingHaarPreservation B μA hB g).measure_preimage
        (hEmb.measurableSet_image' hs).nullMeasurableSet
    have hWeight : (fun u => (w ((C g).symm u) : ℝ≥0∞)) = fun u => (w u : ℝ≥0∞) := by
      funext u
      rw [hw, hw]
      let δ : Aˣ →* ℝ≥0 := distribHaarChar A
      have hδ : δ ((C g).symm u) = δ u := by
        change δ (g⁻¹ * (u * g)) = δ u
        calc
          _ = δ u * (δ g⁻¹ * δ g) := by rw [map_mul, map_mul]; ac_rfl
          _ = δ u := by rw [← map_mul, inv_mul_cancel, map_one, mul_one]
      rw [show distribHaarChar A ((C g).symm u) = distribHaarChar A u from hδ]
    change (r.withDensity fun u => (w u : ℝ≥0∞)).map (C g).toMeasurableEquiv = η
    rw [Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_equiv]
    change (r.map (C g)).withDensity (fun u => (w ((C g).symm u) : ℝ≥0∞)) = η
    rw [hr, hWeight]
  have : η.IsMulRightInvariant := by
    constructor
    intro g
    have hR : (· * g) = (C g⁻¹) ∘ (g * ·) := by
      funext x
      change x * g = g⁻¹ * (g * x) * (g⁻¹)⁻¹
      rw [inv_inv, inv_mul_cancel_left]
    rw [hR, ← Measure.map_map (C g⁻¹).continuous.measurable (measurable_const_mul g),
      map_mul_left_eq_self, hConj]
  have hScale := Measure.isMulLeftInvariant_eq_smul μ η
  constructor
  intro g
  rw [hScale, Measure.map_smul _ (measurable_mul_const g).aemeasurable, map_mul_right_eq_self]

end Langlands.HarmonicAnalysis.UnitConjugation
