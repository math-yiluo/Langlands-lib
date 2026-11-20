import Langlands.Representation.Plancherel.FormalDegreeHaarScaling
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Haar comparison for the same discrete-series class on Borel quotients -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Plancherel

universe uG uV

section Fixed

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (A : Subgroup H) [A.Normal] (hA : A ≤ Subgroup.center H)
  [MeasurableSpace (H ⧸ A)] [BorelSpace (H ⧸ A)]
  [LocallyCompactSpace (H ⧸ A)] [SecondCountableTopology (H ⧸ A)]
  (mu eta : Measure (H ⧸ A)) [mu.IsHaarMeasure] [eta.IsHaarMeasure]

/-- Haar normalization does not change the predicate on the same smooth class. -/
theorem isDiscreteSeriesClass_haar_iff
    (omega : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := H)) :
    IsDiscreteSeriesClass A hA mu omega ↔ IsDiscreteSeriesClass A hA eta omega := by
  obtain ⟨c, hc, heq⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ eta = c • mu :=
    ⟨Measure.haarScalarFactor eta mu,
      (Measure.haarScalarFactor_pos_of_isHaarMeasure eta mu).ne',
      Measure.isMulLeftInvariant_eq_smul eta mu⟩
  subst eta
  let : NeZero c := ⟨hc⟩
  exact (isDiscreteSeriesClass_smul_measure_iff A hA mu c omega).symm

end Fixed

section Transport

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H]

/-- Equal central subgroups and two Borel quotient presentations give the
same predicate on each identical smooth representation class. -/
theorem isDiscreteSeriesClass_borel_quotient_eq_iff
    (A B : Subgroup H) [nA : A.Normal] [nB : B.Normal]
    (hA : A ≤ Subgroup.center H) (hB : B ≤ Subgroup.center H) (hAB : A = B)
    (mA : MeasurableSpace (H ⧸ A)) (mB : MeasurableSpace (H ⧸ B))
    [bA : @BorelSpace (H ⧸ A) inferInstance mA]
    [bB : @BorelSpace (H ⧸ B) inferInstance mB]
    (mu : @Measure (H ⧸ A) mA) (eta : @Measure (H ⧸ B) mB)
    [hm : mu.IsHaarMeasure] [he : eta.IsHaarMeasure]
    (omega : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := H)) :
    @IsDiscreteSeriesClass.{uG, uV} H _ _ _ A nA hA mA mu hm omega ↔
      @IsDiscreteSeriesClass.{uG, uV} H _ _ _ B nB hB mB eta he omega := by
  subst B
  have hmAB : mA = mB := bA.measurable_eq.trans bB.measurable_eq.symm
  subst mB
  let : MeasurableSpace (H ⧸ A) := mA
  exact isDiscreteSeriesClass_haar_iff A hA mu eta omega

end Transport

end Langlands.Plancherel
