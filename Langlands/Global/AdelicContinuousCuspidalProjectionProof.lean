import Langlands.Global.AdelicContinuousCuspidalProjectionAssembly
import Langlands.Global.AdelicLeviRadicalAverageTestFunctionProof
import Langlands.Global.AdelicNormOnePartialConvolutionDecayProof

/-! # Continuous cuspidal projections of automorphic functions -/

universe u

namespace Langlands.Global

/-- Every automorphic function on a standard parabolic quotient has a continuous, moderate,
relatively cuspidal projection characterized by the absolutely convergent norm-one Levi
pairings of Bernstein–Lapid (6.8). -/
theorem continuousCuspidalProjectionExistence : ContinuousCuspidalProjectionExistenceStatement.{u} :=
  continuousCuspidalProjectionExistence_of_analyticInputs
    leviRadicalAverageTestFunction normOnePartialConvolutionRapidDecay

end Langlands.Global
