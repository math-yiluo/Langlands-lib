import Langlands.Global.AdelicAutomorphicExponentDecompositionStatement
import Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement

/-! # The exponent decomposition from Harish-Chandra's finiteness theorem: the implication -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- Harish-Chandra's finiteness theorem on parabolic quotients `V(𝔸)M'(F) \ G(𝔸)`
(`ParabolicHarishChandraFinitenessStatement`) implies the exponent decomposition of automorphic
functions on the standard parabolic quotients `U_Q(𝔸) M_Q(F) \ G(𝔸)`
(`AutomorphicExponentDecompositionStatement`), in the same universe. -/
def AutomorphicExponentDecompositionReductionStatement : Prop :=
  Langlands.Automorphic.GroupSchemeFunctions.ParabolicHarishChandraFinitenessStatement.{u} →
    AutomorphicExponentDecompositionStatement.{u}

end Langlands.Global
