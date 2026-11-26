import Langlands.Global.Arithmetic.HarrisProposition48MultiplicityStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchReductionProof
import Langlands.Global.Arithmetic.HarrisProposition48MackeyFibreProof
import Langlands.Global.Arithmetic.HarrisProposition48MackeyGaloisProof
import Langlands.Global.Arithmetic.HarrisProposition48MackeyChildTransportProof
import Langlands.Global.Arithmetic.HarrisProposition48PrimeInducedParameterStagesProof
import Langlands.Global.Arithmetic.HarrisProposition48PrimeInductionStagesProof
import Langlands.Global.Arithmetic.HarrisProposition48InducedParameterRegularAlgebraicProof
import Langlands.Global.Arithmetic.HarrisWeakInductionConjugateSelfDualTCProof
import Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterProof
import Langlands.Automorphic.ArithmeticComapSupercuspidalComponentProof
import Langlands.Global.Arithmetic.HarrisConjugateSelfDualUnitaryCentralCharacterProof
import Langlands.Global.Arithmetic.HarrisConjugateSelfDualSupercuspidalConjPlaceProof
import Langlands.Global.Arithmetic.HarrisSplitPlaceNeConjPlaceProof

/-!
# Proof of the totally complex exact-stabilizer prime branch with multiplicity

Proves `Proposition48ExactStabilizerMultiplicityPrimeBranchTCStatement`, the totally
complex form of the prime-orbit branch of the induction for Harris (1998),
Proposition 4.8 (printed p.203), under condition (4.12), with Harris's Theorem 1.2 with
multiplicity (`Harris1998Theorem12CuspidalMultiplicityStatement`) among its premises.
The proof applies the common prime-orbit argument
`proposition48ExactStabilizerPrimeBranch_of_inputs` to the proofs of its twelve
interfaces, to the totally complex self-duality interface applied to the premise
`CuspidalSpectralRigidityTCStatement`, and to the totally complex premises B2 and B4
directly. Theorem 1.2 with multiplicity, totally complex isobaric invariance, totally
complex B3 and the premise `Q.IsSpaced` are not used.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- The exact target `Proposition48ExactStabilizerMultiplicityPrimeBranchTCStatement`.
The totally complex forms of B2 and B4 are the inputs of the common argument; the
remaining inputs are the proved interfaces, the totally complex self-duality interface
applied to the given rigidity, restricted B7 and the bridge. -/
theorem proposition48ExactStabilizerMultiplicityPrimeBranchTC :
    Proposition48ExactStabilizerMultiplicityPrimeBranchTCStatement.{uF, uV} := by
  intro _ hRig _ hB2 _ hB4 hB7 hBridge Q D hQ _ hstep hcard hdist hchild
  exact proposition48ExactStabilizerPrimeBranch_of_inputs
    proposition48MackeyFibre proposition48MackeyConstituentGaloisConjugate
    proposition48MackeyChildTransport proposition48PrimeInducedParameterStages
    proposition48PrimeInductionStages proposition48InducedParameterRegularAlgebraic
    arithmeticComapUnitaryCentralCharacter arithmeticComapSupercuspidalComponent
    conjugateSelfDualUnitaryCentralCharacter conjugateSelfDualSupercuspidalConjPlace
    splitPlaceNeConjPlace (weakInductionConjugateInverseSelfDualTC hRig)
    hB2 hB4 hB7 hBridge Q D hQ hstep hcard hdist hchild

end Langlands.Global.Harris
