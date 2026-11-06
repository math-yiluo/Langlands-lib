import Langlands.Global.CompactDiscreteQuotientUnimodularityStatement

/-! # Right-invariant Haar from a compact discrete quotient -/

noncomputable section

universe u

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Langlands.Global

/-- Finite nonzero mass of a strict Borel transversal forces every right modular factor to one. -/
theorem compactDiscreteQuotientHaarRightInvariant :
    CompactDiscreteQuotientHaarRightInvariantStatement.{u} := by
  intro H _ _ _ _ _ _ _ Γ hΓ hcompact
  let : CompactSpace (LeftCosetSpace Γ) := hcompact
  let : Countable Γ := LeftCosetSpace.countable_of_isDiscrete Γ hΓ
  let measureQ := LeftCosetSpace.haarQuotientMeasure Γ hΓ
  let : IsLocallyFiniteMeasure measureQ :=
    LeftCosetSpace.isLocallyFiniteMeasure_haarQuotientMeasure Γ hΓ
  let : IsFiniteMeasure measureQ := inferInstance
  let s := LeftCosetSpace.fundamentalDomain Γ hΓ
  have hsMeas : MeasurableSet s := LeftCosetSpace.measurableSet_fundamentalDomain Γ hΓ
  have hs : IsFundamentalDomain Γ s (Measure.haar : Measure H) :=
    LeftCosetSpace.isFundamentalDomain Γ hΓ _
  have hmass : measureQ univ = (Measure.haar : Measure H) s :=
    LeftCosetSpace.quotientMeasure_univ Γ _ s
  have hmass0 : (Measure.haar : Measure H) s ≠ 0 := by
    rw [← hmass]
    exact fun h => LeftCosetSpace.haarQuotientMeasure_ne_zero Γ hΓ
      (Measure.measure_univ_eq_zero.mp h)
  have hmassTop : (Measure.haar : Measure H) s ≠ ⊤ := by
    rw [← hmass]
    exact measure_ne_top measureQ univ
  refine ⟨fun g => ?_⟩
  have htMeas : MeasurableSet ((fun x : H => x * g) ⁻¹' s) :=
    hsMeas.preimage (measurable_id.mul_const g)
  have ht : IsFundamentalDomain Γ ((fun x : H => x * g) ⁻¹' s)
      (Measure.haar : Measure H) := by
    refine IsFundamentalDomain.mk' htMeas.nullMeasurableSet (fun x => ?_)
    change ∃! γ : Γ, ((γ : H) * x) * g ∈ s
    simpa only [mul_assoc] using LeftCosetSpace.fundamentalDomain_unique Γ hΓ (x * g)
  have hscale : ((Measure.modularCharacterFun g : ℝ≥0) : ℝ≥0∞) *
      (Measure.haar : Measure H) s = (Measure.haar : Measure H) s := by
    calc
      _ = (Measure.map (fun x : H => x * g) Measure.haar) s := by
        rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
        simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      _ = (Measure.haar : Measure H) ((fun x : H => x * g) ⁻¹' s) :=
        Measure.map_apply (measurable_id.mul_const g) hsMeas
      _ = (Measure.haar : Measure H) s := ht.measure_eq hs
  have hfactor : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hmass0 hmassTop).mp (by simpa only [one_mul] using hscale)
  have hfactorNN : Measure.modularCharacterFun g = 1 := by exact_mod_cast hfactor
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul, hfactorNN, one_smul]

end Langlands.Global
