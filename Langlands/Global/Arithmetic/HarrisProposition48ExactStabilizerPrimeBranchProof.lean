import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchReductionProof
import Langlands.Global.Arithmetic.HarrisProposition48MackeyFibreProof
import Langlands.Global.Arithmetic.HarrisProposition48MackeyGaloisProof
import Langlands.Global.Arithmetic.HarrisProposition48MackeyChildTransportProof
import Langlands.Global.Arithmetic.HarrisProposition48PrimeInducedParameterStagesProof
import Langlands.Global.Arithmetic.HarrisProposition48PrimeInductionStagesProof
import Langlands.Global.Arithmetic.HarrisProposition48InducedParameterRegularAlgebraicProof
import Langlands.Global.Arithmetic.HarrisWeakInductionConjugateSelfDualProof
import Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterProof
import Langlands.Automorphic.ArithmeticComapSupercuspidalComponentProof
import Langlands.Global.Arithmetic.HarrisConjugateSelfDualUnitaryCentralCharacterProof
import Langlands.Global.Arithmetic.HarrisConjugateSelfDualSupercuspidalConjPlaceProof
import Langlands.Global.Arithmetic.HarrisSplitPlaceNeConjPlaceProof

/-!
# Proof of the exact-stabilizer prime branch of Proposition 4.8

Proves `Proposition48ExactStabilizerPrimeBranchStatement`, the prime-orbit branch
of the induction for Harris (1998), Proposition 4.8 (printed p.203), under the
exact-stabilizer condition (4.12). The reduction
`proposition48ExactStabilizerPrimeBranchReduction` is applied to the Library's
proofs of its twelve interfaces. The premises of the branch itself (Theorem 1.2,
rigidity, isobaric invariance, B2, B3, B4, restricted B7 and the archimedean
bridge) stay premises of the target.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- The exact target `Proposition48ExactStabilizerPrimeBranchStatement`: the
reduction `proposition48ExactStabilizerPrimeBranchReduction` applied to the
proofs of its twelve interfaces. -/
theorem proposition48ExactStabilizerPrimeBranch :
    Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV} :=
  proposition48ExactStabilizerPrimeBranchReduction.{uF, uV}
    proposition48MackeyFibre.{uF}
    proposition48MackeyConstituentGaloisConjugate.{uF, uV}
    proposition48MackeyChildTransport.{uF, uV}
    proposition48PrimeInducedParameterStages.{uF}
    proposition48PrimeInductionStages.{uF, uV}
    proposition48InducedParameterRegularAlgebraic.{uF}
    weakInductionConjugateInverseSelfDual.{uV, 0, 0}
    arithmeticComapUnitaryCentralCharacter.{0, 0}
    arithmeticComapSupercuspidalComponent.{0, 0, uV}
    conjugateSelfDualUnitaryCentralCharacter.{0}
    conjugateSelfDualSupercuspidalConjPlace.{0, uV}
    splitPlaceNeConjPlace.{0}

end Langlands.Global.Harris
