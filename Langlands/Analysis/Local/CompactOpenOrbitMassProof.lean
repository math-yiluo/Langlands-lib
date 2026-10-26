import Langlands.Analysis.Local.CompactOpenOrbitMassStatement
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.Analysis.Local.QuotientMass

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure

universe uG

/-- Exact published compact-open orbit averaging and mass statement. -/
theorem compactOpenOrbitMass : CompactOpenOrbitMassStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ _ _ μG μH _ _ _ _ _ K hK ν hν q Ω A a
  obtain ⟨hcpos, hcfin, hres⟩ := compactOpenOrbitMeasure H hH μG μH K hK ν hν 1
  have hS : {h : H | (1 : G)⁻¹ * (h : G) * 1 ∈ K} = A := by
    ext h
    simp [A]
  have hC : (fun k : G => q (1 * k)) '' (K : Set G) = Ω := by
    simp only [one_mul]
    rfl
  have hK1 : {x : G | (1 : G)⁻¹ * x ∈ K} = (K : Set G) := by
    ext x
    simp
  rw [hS] at hcpos hcfin
  have hΩo : IsOpen Ω := isOpen_compactOpenQuotientOrbit H K
  have hmass : ν Ω = μG (K : Set G) / μH A := by
    have hq : Continuous (fun k : G => q (1 * k)) :=
      (leftQuotient_isOpenQuotientMap H).continuous.comp (continuous_const.mul continuous_id)
    have huniv := congrArg (fun m : Measure (LeftQuotient H) => m Set.univ) hres
    rw [hC, hS, Measure.restrict_apply_univ, Measure.smul_apply,
      Measure.map_apply hq.measurable MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ, smul_eq_mul] at huniv
    rw [huniv, ENNReal.div_eq_inv_mul]
  refine ⟨isCompact_compactOpenQuotientOrbit H K hK, hΩo,
    hS ▸ isCompact_compactOpenOrbitStabilizer H hH K hK 1,
    hS ▸ isOpen_compactOpenOrbitStabilizer H K 1,
    hcpos, hcfin, (hν.compactOpenQuotientOrbit_mass K hK).1,
    (hν.compactOpenQuotientOrbit_mass K hK).2, ?_, hmass, ?_⟩
  · intro x
    have hx := quotientAverage_compactOpen_leftCoset_indicator H μH K 1 x
    rw [hK1, hS] at hx
    rw [hx]
    change ((fun k : G => q (1 * k)) '' (K : Set G)).indicator _ x = _
    rw [hC]
    by_cases hxΩ : x ∈ Ω <;> simp [hxΩ, a]
  · rw [integral_indicator_const _ hΩo.measurableSet, measureReal_def, hmass,
      ENNReal.toReal_div, Complex.real_smul, mul_one]

end Langlands.QuotientIntegration
