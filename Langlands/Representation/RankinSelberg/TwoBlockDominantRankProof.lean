import Langlands.Representation.RankinSelberg.TwoBlockDominantRankTransport
import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictLContinuation
import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictGammaContinuation

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open DominantRankTransport

universe uF uV uW

/-- The actual lower-induction L conclusion, including the equal-rank boundary. -/
theorem lowerLDominant : LowerLDominantInput.{uF,uV,uW} := by
  intro p hp F ψ ν r t m h V _ _ W _ _ π σ htr hπ hσ
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  have hB : StrictTwoBlockSymmetricLBound F h ψ ν π σ := by
    rcases lt_or_eq_of_le htr with hlt | heq
    · exact strictTwoBlockSymmetricLBound_at_zero F h hlt ψ ν π σ hπ hσ
    · subst r
      exact equalTwoBlockSymmetricLBound_at_zero F h ψ ν π σ hπ hσ
  obtain ⟨P, P0, P1, hP, hP0, hP1, Q, e, hdiv⟩ := hB
  refine ⟨P, ![P0, P1], hP, ?_, Q, e, ?_⟩
  · intro i
    fin_cases i
    · exact hP0
    · exact hP1
  · simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using hdiv

/-- The exact published dominant-rank L target, transported through the actual
normalized lower-to-upper equivalence with the complete block family reversed. -/
theorem twoBlockLDominantRank : TwoBlockLDominantRankStatement.{uF,uV,uW} :=
  lDominant_of_lower lowerLDominant

/-- The actual lower-induction gamma conclusion, including the equal boundary. -/
theorem lowerGammaDominant : LowerGammaDominantInput.{uF,uV,uW} := by
  intro p hp F ψ ν r t m h V _ _ W _ _ π σ htr hπ hσ
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  have hB : StrictTwoBlockSymmetricGammaProduct F h ψ ν π σ := by
    rcases lt_or_eq_of_le htr with hlt | heq
    · exact strictTwoBlockSymmetricGammaProduct_at_zero F h hlt ψ ν π σ hπ hσ
    · subst r
      exact equalTwoBlockSymmetricGammaProduct_at_zero F h ψ ν π σ hπ hσ
  obtain ⟨G0, G1, hG0, hG1, hG⟩ := hB
  refine ⟨![G0, G1], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hG0
    · exact hG1
  · simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using hG

/-- The exact published dominant-rank gamma target, transported through the
actual normalized lower-to-upper equivalence of the complete reversed family. -/
theorem twoBlockGammaDominantRank : TwoBlockGammaDominantRankStatement.{uF,uV,uW} :=
  gammaDominant_of_lower lowerGammaDominant

end Langlands.RankinSelberg
