import Langlands.Representation.Classification.IntegralCuspidalJacquetWordLocalMovesStatement
import Langlands.Representation.Classification.IntegralCuspidalJacquetWordAdapters

/-! # Conditional local moves for actual integral cuspidal Jacquet words -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

theorem integralCuspidalJacquetWordLocalMoves :
    IntegralCuspidalJacquetWordLocalMoves.{uF,uV} F T := by
  intro hinterchange hirreducible htransfer
  let := T.topology
  intro m n A π hπ hAdm hFL
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro l r a b hab hba hword
    exact integralCuspidalJacquetWord_unlinked_pair F T hinterchange hirreducible
      hπ hAdm hFL l r a b hba.symm hab.symm hword
  · exact integralCuspidalJacquetWord_lower_repeat F T htransfer hπ hAdm hFL
  · exact integralCuspidalJacquetWord_upper_repeat F T htransfer hπ hAdm hFL

end Langlands.Classification
