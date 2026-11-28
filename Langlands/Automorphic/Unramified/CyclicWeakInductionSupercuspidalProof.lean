import Langlands.Automorphic.Unramified.CyclicWeakInductionSupercuspidalPairEquations
import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedGenerationProof
import Langlands.Global.RankinSelberg.EqualSemilocalEquationFromOrdinaryTests
import Langlands.Global.RankinSelberg.EqualSemilocalEquationTCFromOrdinaryTests
import Langlands.Global.RankinSelberg.RealEqualOrdinaryPlaceTestsProof

/-! # Unique-place supercuspidality of cyclic weak automorphic induction -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global.RankinSelbergGlobal

/-- A supplied cyclic weak induction has a supercuspidal component at the distinguished
finite place under the unique-place arithmetic orbit hypotheses. -/
theorem cyclicWeakInductionSupercuspidal :
    CyclicWeakInductionSupercuspidalStatement.{uF,uE,uV,uW} :=
  (cyclicWeakInductionSupercuspidalFromEqualSemilocal
    (equalSemilocalEquationFromOrdinaryTests.{uF,uV} realEqualOrdinaryPlaceTestsPositiveRank
      (complexOrdinaryPlaceTests_of_generation complexOrdinaryNormalizedGeneration
        complexWhittakerRestrictionOnto).2)
    (equalSemilocalEquationFromOrdinaryTests.{uE,uW} realEqualOrdinaryPlaceTestsPositiveRank
      (complexOrdinaryPlaceTests_of_generation complexOrdinaryNormalizedGeneration
        complexWhittakerRestrictionOnto).2)).1

end Langlands.Automorphic.Unramified
