import Langlands.BushnellKutzko.SupercuspidalSwanLevelStatement
import Langlands.BushnellKutzko.SwanLevelRankOne
import Langlands.BushnellKutzko.SwanLevelHigherRank

/-! # Proof of T2: the Swan conductor of a supercuspidal is rank times normalized level

Bushnell (1987), Theorem 3, printed p. 198; Bushnell–Fröhlich (1985), (3.3.8), printed p. 258;
operator route note, Proposition `prop:T2`. The rank-one case is
`exists_firstFixedLevel_eq_of_isNormalizedLevel_rankOne` (module `SwanLevelRankOne`), the case
of rank at least two is `exists_firstFixedLevel_eq_of_isNormalizedLevel` (module
`SwanLevelHigherRank`).
-/

noncomputable section

namespace Langlands.BushnellKutzko

universe uK uV

/-- **T2.** For every supercuspidal class `π` of `GL_{k+1}(K)` with normalized level `x`, the
conductor `Numerical.conductor K π` is a natural number `c` with `c - (k + 1) = (k + 1) x`
(truncated subtraction). -/
theorem supercuspidalSwanLevel : SupercuspidalSwanLevelStatement.{uK, uV} := by
  intro p _ K k π x hlev
  rcases k with _ | n
  · exact exists_firstFixedLevel_eq_of_isNormalizedLevel_rankOne K π hlev
  · exact exists_firstFixedLevel_eq_of_isNormalizedLevel K n.succ_pos π hlev

end Langlands.BushnellKutzko
