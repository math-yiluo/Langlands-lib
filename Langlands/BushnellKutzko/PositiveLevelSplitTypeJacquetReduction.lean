import Langlands.BushnellKutzko.PositiveLevelSplitTypeJacquetStatement
import Langlands.BushnellKutzko.UnequalPositiveSplitTypeJacquetStatement
import Langlands.BushnellKutzko.DiagonalSplitTypeJacquet

/-! # Reduction of positive-level Jacquet nonvanishing to the case `x > y`

The case of a split type of level `(x, x)` is proved by
`SplitBlocks.diagonalSplitType_jacquet_nonvanishing`; the case `x > y > 0` is the premise.
-/

namespace Langlands.BushnellKutzko

universe uF uπ uρ

/-- Jacquet nonvanishing for split types of level `(x, y)` with `x > y > 0` implies it for
all split types of positive level. -/
def PositiveLevelSplitTypeJacquetReductionStatement : Prop :=
  UnequalPositiveSplitTypeJacquetStatement.{uF, uπ, uρ} →
    PositiveLevelSplitTypeJacquetStatement.{uF, uπ, uρ}

theorem positiveLevelSplitTypeJacquet_of_unequal :
    PositiveLevelSplitTypeJacquetReductionStatement.{uF, uπ, uρ} := by
  intro hU F _ _ _ _ n hn ψF hψ π hirr hadm K ρ hρ hc
  rcases hρ with ⟨x, hx⟩ | ⟨x, y, hxy⟩
  · have hKco := IsGLSplitType.isCompact_isOpen (n := n) (K := K) (ψF := ψF) (ρ := ρ)
      (Or.inl (Or.inl ⟨x, hx⟩))
    exact SplitBlocks.diagonalSplitType_jacquet_nonvanishing π hadm ρ hx hKco.1 hKco.2 hc
  · exact hU F n hn ψF hψ π hirr hadm K ρ x y hxy hc

end Langlands.BushnellKutzko
