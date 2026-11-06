import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LocalOpenCellGamma

/-! # Open-cell gamma with right invariance only along the opposite subgroup -/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Measure Topology

namespace Langlands.HarishChandraSchwartz

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {P V : Subgroup G}
  [LocallyCompactSpace P] [LocallyCompactSpace V]
  [SecondCountableTopology P] [SecondCountableTopology V]
  (μ : Measure G) [IsHaarMeasure μ]
  (μP : Measure P) [IsHaarMeasure μP] (μV : Measure V) [IsHaarMeasure μV]

/-- The pullback of the ambient measure along the existing open-cell map. -/
def openCellPullbackMeasure : Measure (P × V) :=
  Measure.comap openCellMap μ

/-- The local range formula only uses ambient right translations along `V`.
Full ambient right invariance and conullness are unnecessary. -/
theorem exists_lintegral_range_openCellMap_of_rightInvariantOn
    (hright : ∀ v : V, Measure.map (fun g : G => g * (v : G)) μ = μ)
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V))) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g in Set.range (openCellMap (P := P) (V := V)), F g ∂μ =
        c * ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP := by
  have hpre (v : V) (S : Set G) :
      μ ((fun g : G => g * (v : G)) ⁻¹' S) = μ S := by
    calc
      _ = (Measure.map (fun g : G => g * (v : G)) μ) S :=
        ((MeasurableEquiv.mulRight (v : G)).map_apply S).symm
      _ = μ S := by rw [hright v]
  have hme := hι.measurableEmbedding
  set ν : Measure (P × V) := openCellPullbackMeasure μ with hν
  change ν = Measure.comap openCellMap μ at hν
  have hνinv : ν.IsMulLeftInvariant := ⟨fun q => by
    ext S hS
    rw [map_apply (measurable_const_mul q) hS, hν, hme.comap_apply, hme.comap_apply,
      image_preimage_mul_openCellMap,
      show (fun g => (q.1 : G) * g * (q.2 : G)⁻¹) ⁻¹' (openCellMap '' S) =
        (fun g => (q.1 : G) * g) ⁻¹' ((fun g => g * (q.2 : G)⁻¹) ⁻¹'
          (openCellMap '' S)) from rfl,
      measure_preimage_mul]
    simpa only [Subgroup.coe_inv] using hpre (q.2⁻¹) (openCellMap '' S)⟩
  have hνfin : IsFiniteMeasureOnCompacts ν := ⟨fun S hS => by
    rw [hν, hme.comap_apply]
    exact (hS.image hι.continuous).measure_lt_top⟩
  have heq := isMulLeftInvariant_eq_smul ν (μP.prod μV)
  set c := haarScalarFactor ν (μP.prod μV)
  have hint : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g in Set.range (openCellMap (P := P) (V := V)), F g ∂μ =
        c * ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP := by
    intro F hF
    rw [← hme.map_comap μ, hme.lintegral_map, ← hν, heq, lintegral_smul_measure,
      lintegral_prod (fun x => F (openCellMap x))
        (hF.comp hι.continuous.measurable).aemeasurable,
      ENNReal.smul_def, smul_eq_mul]
    rfl
  refine ⟨c, ?_, hint⟩
  rw [pos_iff_ne_zero]
  intro hc
  have h1 := hint (fun _ => 1) measurable_const
  rw [hc, ENNReal.coe_zero, zero_mul, lintegral_const, one_mul,
    Measure.restrict_apply_univ] at h1
  exact (hι.isOpen_range.measure_ne_zero μ ⟨_, Set.mem_range_self (1 : P × V)⟩) h1

include μ in
/-- A compact open meets the open cell in an open neighborhood of one.
Restricted ambient right invariance suffices to make gamma finite and positive. -/
theorem openCellConstant_ne_zero_ne_top_of_rightInvariantOn
    (hright : ∀ v : V, Measure.map (fun g : G => g * (v : G)) μ = μ)
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    openCellConstant μP μV K ≠ 0 ∧ openCellConstant μP μV K ≠ ⊤ := by
  obtain ⟨c, hc, hformula⟩ :=
    exists_lintegral_range_openCellMap_of_rightInvariantOn μ μP μV hright hι
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
