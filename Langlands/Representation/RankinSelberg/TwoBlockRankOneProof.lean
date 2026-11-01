import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationProof
import Langlands.Representation.RankinSelberg.TwoBlockModelGamma
import Langlands.Representation.RankinSelberg.TwoBlockModelLDivisibility
import Langlands.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceProof

/-! # The rank-one test gamma and L analytic bases -/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The full closed rank-one test gamma base for two positive blocks. -/
theorem twoBlockGammaRankOne : TwoBlockGammaRankOneStatement.{uF,uV,uW} :=
  twoBlockGammaRankOne_of_generic_matrix
    GodementJacquet.genericMatrixFunctionalEquation.{uF,uF}

/-- The full closed rank-one test L base for two positive blocks. -/
theorem twoBlockLRankOne : TwoBlockLRankOneStatement.{uF,uV,uW} :=
  twoBlockLRankOne_of_uniform_mellin uniformFiniteFunctionMellinConvergence

end Langlands.RankinSelberg
