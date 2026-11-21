import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryRankOneProof
import Langlands.Global.Arithmetic.HarrisProposition48RankOneStatement

/-! # The full-datum rank-one case of Harris's Proposition 4.8 -/

universe uF uV

namespace Langlands.Global.Harris

/-- The full-datum rank-one case follows by extracting auxiliary-place validity. -/
theorem proposition48RankOne :
    Proposition48RankOneStatement.{uF, uV} := by
  intro Q hValid hRank
  rcases hValid with ⟨hReciprocity, hDatum⟩
  rcases hDatum with
    ⟨hSplit, hTower, hNormal, _, _, _, _, hAbove, hCompatible, hUnique, hUniqueConj,
      _, _, hGeneralPosition, hAlgebraic, hRegular, hConjugateInverse, _, hComponent⟩
  have hAuxiliary : Q.IsAuxiliaryValid :=
    ⟨hReciprocity, hSplit, hTower, hNormal, hAbove, hCompatible, hUnique, hUniqueConj,
      hGeneralPosition, hAlgebraic, hRegular, hConjugateInverse, hComponent⟩
  exact proposition48AuxiliaryRankOne.{uF, uV} Q hAuxiliary hRank

end Langlands.Global.Harris
