import Langlands.Global.AdelicEisensteinUniformCuspidalExpansionReductionStatement
import Langlands.Global.AdelicEisensteinUniformCuspidalExpansionIdentity
import Langlands.Global.CuspidalTestExpansion.Reduction
import Langlands.Global.AdelicConstantTermAutomorphyProof
import Langlands.Global.AdelicLeviCuspFormRapidDecayProof
import Langlands.Global.AdelicAutomorphicExponentDecompositionReduction

/-! # The uniform cuspidal expansion for finite families from its analytic inputs

`eisensteinUniformCuspidalExpansion_of_inputs` proves `EisensteinUniformCuspidalExpansionStatement`
from `ConstantTermAutomorphyStatement`, `AutomorphicExponentDecompositionStatement` and
`LeviCuspFormRapidDecayStatement`, and `eisensteinUniformCuspidalExpansionReduction` records this
as a proof of `EisensteinUniformCuspidalExpansionReductionStatement`. With the Library proofs
`constantTermAutomorphy` and `leviCuspFormRapidDecay`,
`eisensteinUniformCuspidalExpansion_of_exponentDecomposition` leaves the exponent decomposition
as the only input, and with the Library theorem
`automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness`,
`eisensteinUniformCuspidalExpansion_of_parabolicHarishChandraFiniteness` derives the statement from
Harish-Chandra's finiteness theorem for parabolic subgroups. -/

universe u

namespace Langlands.Global

/-- The three inputs give the uniform convergent expansion
(`convergentCuspidalTestExpansion_uniform_of_inputs`); its identity case is the one-function
statement, and the finite-family statement follows from that. -/
theorem eisensteinUniformCuspidalExpansion_of_inputs
    (hAut : ConstantTermAutomorphyStatement.{u})
    (hDec : AutomorphicExponentDecompositionStatement.{u})
    (hDecay : LeviCuspFormRapidDecayStatement.{u}) :
    EisensteinUniformCuspidalExpansionStatement.{u} :=
  eisensteinUniformCuspidalExpansion_of_one
    (eisensteinUniformCuspidalExpansionOne_of_uniform
      (convergentCuspidalTestExpansion_uniform_of_inputs hAut hDec hDecay))

/-- `EisensteinUniformCuspidalExpansionReductionStatement` holds. -/
theorem eisensteinUniformCuspidalExpansionReduction :
    EisensteinUniformCuspidalExpansionReductionStatement.{u} :=
  eisensteinUniformCuspidalExpansion_of_inputs

/-- The exponent decomposition alone gives the uniform cuspidal expansion: the other two inputs
are the Library theorems `constantTermAutomorphy` and `leviCuspFormRapidDecay`. -/
theorem eisensteinUniformCuspidalExpansion_of_exponentDecomposition
    (hDec : AutomorphicExponentDecompositionStatement.{u}) :
    EisensteinUniformCuspidalExpansionStatement.{u} :=
  eisensteinUniformCuspidalExpansion_of_inputs constantTermAutomorphy hDec leviCuspFormRapidDecay

/-- Harish-Chandra's finiteness theorem for parabolic subgroups gives the uniform cuspidal
expansion, through the exponent decomposition
(`automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness`). -/
theorem eisensteinUniformCuspidalExpansion_of_parabolicHarishChandraFiniteness
    (hHC :
      Langlands.Automorphic.GroupSchemeFunctions.ParabolicHarishChandraFinitenessStatement.{u}) :
    EisensteinUniformCuspidalExpansionStatement.{u} :=
  eisensteinUniformCuspidalExpansion_of_exponentDecomposition
    (automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness hHC)

end Langlands.Global
