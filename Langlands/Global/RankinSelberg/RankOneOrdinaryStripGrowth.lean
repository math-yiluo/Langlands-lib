import Langlands.Global.RankinSelberg.RankOneOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness
import Langlands.Global.RankinSelberg.RealRankZeroStripGrowth
import Langlands.Global.RankinSelberg.ComplexRankZeroStripGrowth

/-! # Normalized strip growth for all rank-one ordinary archimedean tests -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal LocalFactor.Archimedean
open FunctionalEquationComparison.CompletedEquationAdapter
  (realPairLFactor_denominator_ne_zero complexPairLFactor_denominator_ne_zero)

/-- For every real and complex rank-one ordinary test, an entire normalization exists and
all entire ordinary normalizations have exponential strip growth. -/
def RankOneOrdinaryStripGrowthStatement : Prop :=
  (∀ (d e : List RealBlock), realRank d = 1 → realRank e = 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData 0),
      HasEntireOrdinaryNormalizations (realOrdinaryEqualTest 0 d e a D) (realPairLFactor d e) ∧
        HasOrdinaryNormalizationStripGrowth (realOrdinaryEqualTest 0 d e a D) (realPairLFactor d e)) ∧
  ∀ (d e : List ComplexCharacterData), d.length = 1 → e.length = 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData 0),
      HasEntireOrdinaryNormalizations (complexOrdinaryEqualTest 0 d e a D) (complexPairLFactor d e) ∧
        HasOrdinaryNormalizationStripGrowth (complexOrdinaryEqualTest 0 d e a D)
          (complexPairLFactor d e)

theorem rankOneOrdinaryStripGrowth : RankOneOrdinaryStripGrowthStatement := by
  constructor
  · intro d e hd he a D
    obtain ⟨c, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hd
    obtain ⟨c', rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one he
    refine ordinaryNormalizationGrowthFromExistence _ _ (realPairLFactor_denominator_ne_zero _ _) ?_
    rintro ⟨W, V, Φ⟩
    obtain ⟨C, hW⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel W.2
    obtain ⟨C', hV⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel V.2
    exact RealRankZero.realRankZeroStripGrowth D c c' W V C C' hW hV Φ
  · intro d e hd he a D
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hd
    obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp he
    refine ordinaryNormalizationGrowthFromExistence _ _
      (complexPairLFactor_denominator_ne_zero _ _) ?_
    rintro ⟨W, V, Φ⟩
    obtain ⟨C, hW⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel W.2
    obtain ⟨C', hV⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel V.2
    exact ComplexRankZero.complexRankZeroStripGrowth D c c' W V C C' hW hV Φ

end Langlands.Global.RankinSelbergGlobal
