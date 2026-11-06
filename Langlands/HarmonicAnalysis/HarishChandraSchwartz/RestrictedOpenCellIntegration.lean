import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RestrictedOpenCellGamma

/-! # Global open-cell integration from restricted right invariance -/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Measure Topology

namespace Langlands.HarishChandraSchwartz

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {P V : Subgroup G}
  [LocallyCompactSpace P] [LocallyCompactSpace V]
  [SecondCountableTopology P] [SecondCountableTopology V]

/-- Push the existing product of subgroup measures through the actual
open-cell coordinates, without choosing an ambient normalization. -/
def openCellProductPushforward (μP : Measure P) (μV : Measure V) : Measure G :=
  Measure.map (openCellMap (P := P) (V := V)) (μP.prod μV)

variable (μ : Measure G) [IsHaarMeasure μ]
  (μP : Measure P) [IsHaarMeasure μP] (μV : Measure V) [IsHaarMeasure μV]

/-- Conullness upgrades the local range formula to an ambient formula.
Only right translations by elements of `V` must preserve ambient Haar. -/
theorem exists_lintegral_openCellMap_of_rightInvariantOn
    (hright : ∀ v : V, Measure.map (fun g : G => g * (v : G)) μ = μ)
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g, F g ∂μ =
        c * ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP := by
  obtain ⟨c, hc, h⟩ :=
    exists_lintegral_range_openCellMap_of_rightInvariantOn μ μP μV hright hι
  refine ⟨c, hc, fun F hF => ?_⟩
  rw [← h F hF, Measure.restrict_eq_self_of_ae_mem]
  exact measure_eq_zero_iff_ae_notMem.mp hnull |>.mono fun _ hx => not_not.mp hx

/-- The same existing gamma normalizes the global formula, without
a whole-group right-invariance hypothesis. -/
theorem lintegral_eq_openCellConstant_inv_mul_of_rightInvariantOn
    (hright : ∀ v : V, Measure.map (fun g : G => g * (v : G)) μ = μ)
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G))
    (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤) :
    openCellConstant μP μV K ≠ 0 ∧ openCellConstant μP μV K ≠ ⊤ ∧
      ∀ F : G → ℝ≥0∞, Measurable F →
        ∫⁻ g, F g ∂μ = μ K * (openCellConstant μP μV K)⁻¹ *
          ∫⁻ p, ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV ∂μP := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_lintegral_openCellMap_of_rightInvariantOn μ μP μV hright hι hnull
  have hKc := measure_eq_mul_openCellConstant μ μP μV hc hK
  have hc0' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  have hγ0 : openCellConstant μP μV K ≠ 0 := by
    intro h
    rw [h, mul_zero] at hKc
    exact hK0 hKc
  have hγtop : openCellConstant μP μV K ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hc0'] at hKc
    exact hKtop hKc
  refine ⟨hγ0, hγtop, fun F hF => ?_⟩
  rw [hc F hF, hKc, mul_assoc (c : ℝ≥0∞),
    ENNReal.mul_inv_cancel hγ0 hγtop, mul_one]

/-- The global formula is an equality of actual measures, with its
coefficient fixed by the existing compact-indicator gamma. -/
theorem measure_eq_openCellConstant_inv_smul_of_rightInvariantOn
    (hright : ∀ v : V, Measure.map (fun g : G => g * (v : G)) μ = μ)
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G))
    (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤) :
    μ = (μ K * (openCellConstant μP μV K)⁻¹) •
      openCellProductPushforward μP μV := by
  obtain ⟨_, _, h⟩ :=
    lintegral_eq_openCellConstant_inv_mul_of_rightInvariantOn μ μP μV
      hright hι hnull hK hK0 hKtop
  apply Measure.ext_of_lintegral
  intro F hF
  rw [h F hF, lintegral_smul_measure, openCellProductPushforward,
    lintegral_map hF hι.continuous.measurable,
    lintegral_prod (fun x => F (openCellMap x))
      (hF.comp hι.continuous.measurable).aemeasurable]
  rfl

end Langlands.HarishChandraSchwartz
