import Langlands.Representation.RankinSelberg.TwoBlockModelLDivisibility
import Langlands.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceProof

/-! # The rank-one test L analytic base -/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The full closed rank-one test L base for two positive blocks. -/
theorem twoBlockLRankOne : TwoBlockLRankOneStatement.{uF,uV,uW} :=
  twoBlockLRankOne_of_uniform_mellin uniformFiniteFunctionMellinConvergence

end Langlands.RankinSelberg
