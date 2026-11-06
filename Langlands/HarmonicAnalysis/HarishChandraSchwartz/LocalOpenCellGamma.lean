import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellIntegration

/-! # Local finiteness of the open-cell gamma -/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Measure Topology

namespace Langlands.HarishChandraSchwartz

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {P V : Subgroup G}
  [LocallyCompactSpace P] [LocallyCompactSpace V]
  [SecondCountableTopology P] [SecondCountableTopology V]
  (μ : Measure G) [IsHaarMeasure μ] [μ.IsMulRightInvariant]
  (μP : Measure P) [IsHaarMeasure μP] (μV : Measure V) [IsHaarMeasure μV]

omit [IsHaarMeasure μ] [μ.IsMulRightInvariant] in
/-- Integrating the compact indicator in the local range formula identifies
the gamma with the mass of the compact's intersection with the open cell. -/
theorem measure_inter_range_eq_mul_openCellConstant {c : ℝ≥0}
    (hc : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g in Set.range (openCellMap (P := P) (V := V)), F g ∂μ =
        c * ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP)
    (K : OpenSubgroup G) :
    μ ((K : Set G) ∩ Set.range (openCellMap (P := P) (V := V))) =
      c * openCellConstant μP μV K := by
  have hm : Measurable ((K : Set G).indicator (1 : G → ℝ≥0∞)) :=
    measurable_one.indicator K.isOpen.measurableSet
  have heq := hc _ hm
  rw [lintegral_indicator_one K.isOpen.measurableSet,
    Measure.restrict_apply K.isOpen.measurableSet] at heq
  rw [heq, openCellConstant, lintegral_lintegral_swap]
  · rfl
  · have hcont : Continuous (fun x : P × V => (x.1 : G) * (x.2 : G)⁻¹) := by
      fun_prop
    exact (hm.comp hcont.measurable).aemeasurable

include μ in
/-- A compact open meets the open cell in an open neighborhood of one.
Its finite positive mass implies finite positive gamma without conullness. -/
theorem openCellConstant_ne_zero_ne_top_of_isOpenEmbedding
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    openCellConstant μP μV K ≠ 0 ∧ openCellConstant μP μV K ≠ ⊤ := by
  obtain ⟨c, hc, hformula⟩ := exists_lintegral_range_openCellMap μ μP μV hι
  have heq := measure_inter_range_eq_mul_openCellConstant μ μP μV hformula K
  have hmass0 :
      μ ((K : Set G) ∩ Set.range (openCellMap (P := P) (V := V))) ≠ 0 := by
    apply (K.isOpen.inter hι.isOpen_range).measure_ne_zero μ
    refine ⟨1, K.one_mem, ?_⟩
    exact ⟨(1, 1), by simp [openCellMap]⟩
  have hmasstop :
      μ ((K : Set G) ∩ Set.range (openCellMap (P := P) (V := V))) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hK.measure_lt_top).ne
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  constructor
  · intro hzero
    rw [hzero, mul_zero] at heq
    exact hmass0 heq
  · intro htop
    rw [htop, ENNReal.mul_top hc0] at heq
    exact hmasstop heq

end Langlands.HarishChandraSchwartz
