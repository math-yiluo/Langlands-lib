import Langlands.Representation.RankinSelberg.SupercuspidalProductCompletenessStatement
import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.Assembly
import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.DeltaPairingGL
import Langlands.Representation.Whittaker.GelfandGraevJacquetOpen

/-!
# Whittaker completeness against normalized products of supercuspidals

A compactly supported `ψ`-Whittaker test function of `GL_(n+1)(F)` that integrates to zero against
the Whittaker coefficient functions of every normalized product of irreducible supercuspidal
representations vanishes (Henniart 1993, Lemme 2.1).
-/

namespace Langlands.RankinSelberg

universe uF uW

/-- Whittaker completeness against normalized products of supercuspidals. -/
theorem supercuspidalProductCompleteness : SupercuspidalProductCompletenessStatement.{uF, uW} :=
  SupercuspidalCompleteness.supercuspidalProductCompleteness_of Whittaker.gelfandGraevJacquet
    SupercuspidalCompleteness.deltaPairing

end Langlands.RankinSelberg
