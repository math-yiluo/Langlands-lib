import Langlands.Automorphic.Unramified.CyclicWeakInductionSupercuspidalPairEquations
import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedGenerationProof
import Langlands.Global.RankinSelberg.EqualSemilocalEquationTCFromOrdinaryTests

/-! # Unique-place supercuspidality of cyclic weak induction over totally complex fields -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global.RankinSelbergGlobal

/-- Cyclic weak induction over a totally complex base is supercuspidal at the unique-place
input of the arithmetic orbit criterion. -/
theorem cyclicWeakInductionSupercuspidalTC :
    CyclicWeakInductionSupercuspidalTCStatement.{uF,uE,uV,uW} :=
  cyclicWeakInductionSupercuspidalFromEqualSemilocalTC
    (equalSemilocalEquationTC_of_ordinaryGeneration.{uF,uV} complexOrdinaryNormalizedGeneration)
    (equalSemilocalEquationTC_of_ordinaryGeneration.{uE,uW} complexOrdinaryNormalizedGeneration)

end Langlands.Automorphic.Unramified
