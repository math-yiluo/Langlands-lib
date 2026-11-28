import Langlands.BushnellKutzko.PositiveLevelSplitTypeJacquetReduction
import Langlands.BushnellKutzko.UnequalPositiveSplitTypeJacquet

/-! # Jacquet nonvanishing from a split type of positive level -/

namespace Langlands.BushnellKutzko

universe uF uπ uρ

/-- **BK93 (8.2.5)(iv), nonvanishing.** An irreducible admissible smooth representation
containing a split type with positive second level has a nonzero proper Jacquet module. -/
theorem positiveLevelSplitTypeJacquet : PositiveLevelSplitTypeJacquetStatement.{uF, uπ, uρ} :=
  positiveLevelSplitTypeJacquet_of_unequal SplitBlocks.unequalPositiveSplitTypeJacquet

end Langlands.BushnellKutzko
