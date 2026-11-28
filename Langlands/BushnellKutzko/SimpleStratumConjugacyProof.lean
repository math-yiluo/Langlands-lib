import Langlands.BushnellKutzko.SimpleStratumConjugacyReduction
import Langlands.BushnellKutzko.PureStratumSimpleApproximationProof

/-! # Formal intertwining and conjugacy of simple strata (BK93 (2.6.1)–(2.6.2)) -/

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (2.6.1) and the case of equal orders and levels of BK93 (2.6.2)**, printed
pp. 83–86. -/
theorem simpleStratumConjugacy : SimpleStratumConjugacyStatement.{uF, uV} :=
  simpleStratumConjugacy_of_approximation pureStratumSimpleApproximation

end Langlands.BushnellKutzko
