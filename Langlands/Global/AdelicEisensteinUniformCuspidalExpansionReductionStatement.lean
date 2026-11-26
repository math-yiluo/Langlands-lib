import Langlands.Global.AdelicEisensteinUniformCuspidalExpansionStatement
import Langlands.Global.AdelicConstantTermAutomorphyStatement
import Langlands.Global.AdelicAutomorphicExponentDecompositionStatement
import Langlands.Global.AdelicLeviCuspFormRapidDecayStatement

/-! # The uniform cuspidal expansion for finite families from three named inputs -/

universe u

namespace Langlands.Global

/-- Bernstein–Lapid Corollary 6.10 for finite families with a uniform degree,
`EisensteinUniformCuspidalExpansionStatement`, follows from the automorphy of constant terms
along standard parabolics, the exponent decomposition of automorphic functions on parabolic
quotients, and the rapid decay of cusp forms on standard Levis. -/
def EisensteinUniformCuspidalExpansionReductionStatement : Prop :=
  ConstantTermAutomorphyStatement.{u} → AutomorphicExponentDecompositionStatement.{u} →
    LeviCuspFormRapidDecayStatement.{u} → EisensteinUniformCuspidalExpansionStatement.{u}

end Langlands.Global
