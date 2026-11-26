import Langlands.Global.AdelicConvergentCuspidalTestExpansionStatement
import Langlands.Global.AdelicConstantTermAutomorphyStatement
import Langlands.Global.AdelicAutomorphicExponentDecompositionStatement
import Langlands.Global.AdelicLeviCuspFormRapidDecayStatement

/-! # The convergent cuspidal test expansion from three named inputs -/

universe u

namespace Langlands.Global

/-- The scalar form of Bernstein–Lapid (6.20), `ConvergentCuspidalTestExpansionStatement`,
follows from the automorphy of constant terms along standard parabolics, the exponent
decomposition of automorphic functions on parabolic quotients, and the rapid decay of cusp forms
on standard Levis. -/
def ConvergentCuspidalTestExpansionReductionStatement : Prop :=
  ConstantTermAutomorphyStatement.{u} → AutomorphicExponentDecompositionStatement.{u} →
    LeviCuspFormRapidDecayStatement.{u} → ConvergentCuspidalTestExpansionStatement.{u}

end Langlands.Global
