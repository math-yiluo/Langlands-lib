import Langlands.Representation.RankinSelberg.FiniteLFactorMultiplicativity
import Langlands.Representation.RankinSelberg.TwoBlockLFactorMultiplicativityProof

namespace Langlands.RankinSelberg

universe uF uV uW

/-- JPSS Theorem (3.1)(ii): certified L-polynomial divisibility for actual
normalized induction of any ordered positive block family. -/
theorem lFactorMultiplicativity :
    LFactorMultiplicativityStatement.{uF, uV, uW} :=
  lFactorMultiplicativity_of_twoBlock
    twoBlockLFactorMultiplicativity.{uF, uV, max uF uW}

end Langlands.RankinSelberg
