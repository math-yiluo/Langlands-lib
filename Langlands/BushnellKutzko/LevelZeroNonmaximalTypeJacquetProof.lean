import Langlands.BushnellKutzko.LevelZeroNonmaximalTypeJacquetStatement
import Langlands.BushnellKutzko.LevelZeroSimpleTypeJacquet

/-! # Jacquet nonvanishing for a non-maximal level-zero simple type -/

namespace Langlands.BushnellKutzko

universe uF uρ uπ

/-- **BK93 (7.3.2), first remark, and (7.3.6)(i), kind (b).**
A smooth representation containing a non-maximal level-zero simple type has
nonzero coinvariants along the radical of a proper parabolic. -/
theorem levelZeroNonmaximalTypeJacquet :
    LevelZeroNonmaximalTypeJacquetStatement.{uF, uρ, uπ} := by
  intro F _ _ _ _ n hn J ρ L e hd he2 π hc
  exact LevelZero.levelZero_not_subsingleton_jacquet hn ρ L e hd he2 π hc

end Langlands.BushnellKutzko
