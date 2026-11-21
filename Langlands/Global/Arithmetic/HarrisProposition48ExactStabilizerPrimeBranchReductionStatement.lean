import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerBranchStatement
import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement
import Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement
import Langlands.Automorphic.CuspidalArithmeticTransportStatement

/-!
# Reduction of the exact-stabilizer prime branch of Proposition 4.8

Statements only. The prime-orbit branch of the induction for Harris (1998),
Proposition 4.8, under condition (4.12)
(`Proposition48ExactStabilizerPrimeBranchStatement` and its totally complex
form) follows from twelve named interfaces: the Mackey-step statements of
`HarrisProposition48MackeyTransportStatement`, the arithmetic transport
statements of `CuspidalArithmeticTransportStatement`, and the statements at
the auxiliary conjugate pair of `HarrisAuxiliaryConjugatePairStatement`. The
branch's own premises are kept as premises of the targets. No proof is given
here.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- The exact-stabilizer prime branch follows from the Mackey fibres, Galois
conjugation of Mackey constituents, child transport, parameters and weak
induction in stages, regular algebraicity from induced parameters, conjugate
self-duality of weak inductions of conjugate-inverse characters, arithmetic
transport of unitarity and of supercuspidal components, and the three
statements at the auxiliary conjugate pair. -/
def Proposition48ExactStabilizerPrimeBranchReductionStatement : Prop :=
  Proposition48MackeyFibreStatement.{uF} →
  Proposition48MackeyConstituentGaloisConjugateStatement.{uF, uV} →
  Proposition48MackeyChildTransportStatement.{uF, uV} →
  Proposition48PrimeInducedParameterStagesStatement.{uF} →
  Proposition48PrimeInductionStagesStatement.{uF, uV} →
  Proposition48InducedParameterRegularAlgebraicStatement.{uF} →
  WeakInductionConjugateInverseSelfDualStatement.{uV, 0, 0} →
  ArithmeticComapUnitaryCentralCharacterStatement.{0, 0} →
  ArithmeticComapSupercuspidalComponentStatement.{0, 0, uV} →
  ConjugateSelfDualUnitaryCentralCharacterStatement.{0} →
  ConjugateSelfDualSupercuspidalConjPlaceStatement.{0, uV} →
  SplitPlaceNeConjPlaceStatement.{0} →
    Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV}

/-- The totally complex form: the same interfaces, with the totally complex
form of the conjugate self-duality statement (whose rigidity premise is
`CuspidalSpectralRigidityTCStatement`), give
`Proposition48ExactStabilizerPrimeBranchTCStatement`. -/
def Proposition48ExactStabilizerPrimeBranchReductionTCStatement : Prop :=
  Proposition48MackeyFibreStatement.{uF} →
  Proposition48MackeyConstituentGaloisConjugateStatement.{uF, uV} →
  Proposition48MackeyChildTransportStatement.{uF, uV} →
  Proposition48PrimeInducedParameterStagesStatement.{uF} →
  Proposition48PrimeInductionStagesStatement.{uF, uV} →
  Proposition48InducedParameterRegularAlgebraicStatement.{uF} →
  WeakInductionConjugateInverseSelfDualTCStatement.{uV, 0, 0} →
  ArithmeticComapUnitaryCentralCharacterStatement.{0, 0} →
  ArithmeticComapSupercuspidalComponentStatement.{0, 0, uV} →
  ConjugateSelfDualUnitaryCentralCharacterStatement.{0} →
  ConjugateSelfDualSupercuspidalConjPlaceStatement.{0, uV} →
  SplitPlaceNeConjPlaceStatement.{0} →
    Proposition48ExactStabilizerPrimeBranchTCStatement.{uF, uV}

end Langlands.Global.Harris
