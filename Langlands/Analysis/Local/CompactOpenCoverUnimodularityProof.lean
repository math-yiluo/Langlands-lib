import Langlands.Analysis.Local.CompactOpenCoverUnimodularityStatement

/-!
# Two-sided Haar invariance for compact-open covered groups

Regular Haar uniqueness and cancellation of a compact open subgroup's mass
give right invariance. Closed subgroups inherit the required cover.
-/

namespace Langlands.Haar

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

universe uG

private theorem map_right_eq_self_of_compact_open {G : Type uG} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (hg : g ∈ K) :
    Measure.map (fun x => x * g) μ = μ := by
  have : (Measure.map (fun x => x * g) μ).Regular := Regular.map (Homeomorph.mulRight g)
  have hscale := isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (fun x => x * g) μ) μ
  have hpre : (fun x : G => x * g) ⁻¹' (K : Set G) = K := by
    ext x
    exact K.toSubgroup.mul_mem_cancel_right hg
  have hm := congrArg (fun ν : Measure G => ν (K : Set G)) hscale
  rw [Measure.map_apply (measurable_mul_const g) K.isOpen.measurableSet, hpre,
    Measure.smul_apply] at hm
  have hzero : μ (K : Set G) ≠ 0 := K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩
  have htop : μ (K : Set G) ≠ ⊤ := hK.measure_ne_top
  have he : (haarScalarFactor (Measure.map (fun x => x * g) μ) μ : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hzero htop).mp hm.symm
  rw [ENNReal.coe_eq_one.mp he, one_smul] at hscale
  exact hscale

private theorem rightInvariant_of_compactOpenCover {G : Type uG} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (hcover : ∀ g : G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ g ∈ K)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ] [Regular μ] :
    IsMulRightInvariant μ := by
  refine ⟨fun g => ?_⟩
  obtain ⟨K, hK, hg⟩ := hcover g
  exact map_right_eq_self_of_compact_open μ K hK g hg

/-- Every regular left Haar measure on a compact-open covered group, or on any
closed subgroup with its inherited topology, is right invariant. -/
theorem compactOpenCoverUnimodularity : CompactOpenCoverUnimodularityStatement.{uG} := by
  intro G _ _ _ _ _ hcover
  constructor
  · intro _ _ μ _ _
    exact rightInvariant_of_compactOpenCover hcover μ
  · intro H hH
    have : LocallyCompactSpace H := hH.locallyCompactSpace
    have hcoverH (h : H) :
        ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ h ∈ L := by
      obtain ⟨K, hK, hh⟩ := hcover (h : G)
      let L := OpenSubgroup.comap H.subtype continuous_subtype_val K
      refine ⟨L, ?_, hh⟩
      exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    intro _ _ μH _ _
    exact rightInvariant_of_compactOpenCover hcoverH μH

end Langlands.Haar
