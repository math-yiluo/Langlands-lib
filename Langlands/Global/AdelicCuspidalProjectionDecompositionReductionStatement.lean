import Langlands.Global.AdelicCuspidalProjectionDecompositionStatement
import Langlands.Global.AdelicCuspidalAnnihilator
import Langlands.Global.AdelicConstantTermAutomorphyStatement
import Langlands.Global.AdelicCuspidalProjectionExistenceStatement
import Langlands.Global.AdelicAutomorphicExponentDecompositionStatement

/-! # Reduction of the cuspidal projection decomposition to four inputs -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- Automorphy of constant terms, existence of cuspidal projections, the parabolic cuspidal
vanishing criterion and the exponent decomposition of automorphic functions together give the
unique cuspidal projections of nested constant terms with their finite exponent
decompositions. -/
def CuspidalProjectionDecompositionReductionStatement : Prop :=
  ConstantTermAutomorphyStatement.{u} → CuspidalProjectionExistenceStatement.{u} →
    ParabolicCuspidalVanishingStatement.{u} → AutomorphicExponentDecompositionStatement.{u} →
      CuspidalProjectionDecompositionStatement.{u}

end Langlands.Global
