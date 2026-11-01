import Langlands.Global.ArchimedeanCompactTypeProjectionStatement
import Langlands.Global.ArchimedeanCompactCharacterFixation
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Continuous character projectors for the actual archimedean compact group -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory DerivativeSmoothFunctions CompactWeightedAverage
open scoped ENNReal

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Normalized Haar character averaging gives every actual compact-type projector. -/
theorem compactTypeProjection : CompactTypeProjectionStatement K n := by
  let : MeasurableSpace (standardInfiniteCompact K n) :=
    borel (standardInfiniteCompact K n)
  have : BorelSpace (standardInfiniteCompact K n) := ⟨rfl⟩
  let C : TopologicalSpace.PositiveCompacts (standardInfiniteCompact K n) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let ν : Measure (standardInfiniteCompact K n) := Measure.haarMeasure C
  have : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  have : ν.IsMulLeftInvariant := inferInstance
  have : ν.IsMulRightInvariant := by
    constructor
    intro k
    have h := Measure.isMulInvariant_eq_smul_of_compactSpace (ν.map (· * k)) ν
    have hu := congrArg (fun μ : Measure (standardInfiniteCompact K n) => μ Set.univ) h
    have hc : Measure.haarScalarFactor (ν.map (· * k)) ν = 1 := by
      have hu' : (1 : ℝ≥0∞) =
          (Measure.haarScalarFactor (ν.map (· * k)) ν : ℝ≥0∞) := by
        simpa [Measure.map_apply (continuous_mul_const k).measurable MeasurableSet.univ]
          using hu
      exact_mod_cast hu'.symm
    simpa only [hc, one_smul] using h
  intro σ
  refine ⟨characterAverage ν σ.toContinuousCompactRep, ?_, ?_, ?_, ?_⟩
  · exact characterAverage_mem ν σ.toContinuousCompactRep
  · exact characterAverage_fixes ν σ
  · exact characterAverage_compactAction ν σ.toContinuousCompactRep
  · exact characterAverage_mem_closed_compactOrbit ν σ.toContinuousCompactRep

end Langlands.Global.ArchimedeanGL
