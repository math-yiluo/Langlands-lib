import Langlands.Automorphic.Unramified.CuspidalSpectralArithmeticComapStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralAttachmentExistenceStatement
import Langlands.Automorphic.Unramified.CuspidalWeakBaseChangeTwistStatement
import Langlands.Automorphic.Unramified.CyclicCuspidalFiberStatement
import Langlands.Automorphic.Unramified.CyclicPrimeStableCuspidalDescentStatement
import Langlands.Automorphic.Unramified.CyclicPrimeTwistedCuspidalObstructionStatement
import Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangePairMultiplicityStatement
import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeTransportStatement
import Langlands.Global.Arithmetic.CyclicPrimeNormCharacterRestrictionStatement

/-! # Reduction of cyclic stable descent to prime descent and the twisted cusp obstruction -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global.HeckeCharacter

/-- Prime descent, the prime twisted-cusp obstruction, and the explicit weak-transfer,
fibre, pair and character inputs imply the exact cyclic stable descent proposition. -/
def CyclicStableDescentReductionStatement : Prop :=
  CyclicPrimeStableCuspidalDescentStatement.{uF, uE, uV, uW} →
  CyclicPrimeStableCuspidalDescentStatement.{uE, uE, uW, uW} →
  CyclicPrimeTwistedCuspidalObstructionStatement.{uF, uE} →
  CyclicPrimeTwistedCuspidalObstructionStatement.{uE, uE} →
  CyclicWeakBaseChangePairMultiplicityStatement.{uF, uE, uV, uW} →
  CyclicWeakBaseChangePairMultiplicityStatement.{uE, uE, uW, uW} →
  CyclicCuspidalFiberStatement.{uF, uE, uV, uV} →
  CyclicCuspidalFiberStatement.{uE, uE, uW, uW} →
  CyclicPrimeNormCharacterRestrictionStatement.{uF, uE, uE} →
  CyclicPrimeNormCharacterRestrictionStatement.{uE, uE, uE} →
  IsobaricWeakBaseChangeTowerStatement.{uF, uE, uE, uV, uW, uW} →
  IsobaricWeakBaseChangeTowerStatement.{uE, uE, uE, uW, uW, uW} →
  IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW} →
  CuspidalDeterminantTwistArithmeticComapStatement.{uE, uE} →
  CuspidalWeakBaseChangeNormTwistStatement.{uF, uE, uV, uW} →
  CuspidalSpectralAttachmentExistenceStatement.{uE, uV} →
  CuspidalSpectralAttachmentExistenceStatement.{uE, uW} →
  CuspidalSpectralArithmeticComapStatement.{uF, uE, uV} →
  CuspidalSpectralArithmeticComapStatement.{uE, uE, uW} →
  CyclicStableDescentStatement.{uF, uE, uV, uW}

/-- The descent reduction with totally complex prime descent, twisted obstruction,
and weak base-change pair comparison. -/
def CyclicStableDescentTCReductionStatement : Prop :=
  CyclicPrimeStableCuspidalDescentTCStatement.{uF, uE, uV, uW} →
  CyclicPrimeStableCuspidalDescentTCStatement.{uE, uE, uW, uW} →
  CyclicPrimeTwistedCuspidalObstructionTCStatement.{uF, uE} →
  CyclicPrimeTwistedCuspidalObstructionTCStatement.{uE, uE} →
  CyclicWeakBaseChangePairMultiplicityTCStatement.{uF, uE, uV, uW} →
  CyclicWeakBaseChangePairMultiplicityTCStatement.{uE, uE, uW, uW} →
  CyclicCuspidalFiberStatement.{uF, uE, uV, uV} →
  CyclicCuspidalFiberStatement.{uE, uE, uW, uW} →
  CyclicPrimeNormCharacterRestrictionStatement.{uF, uE, uE} →
  CyclicPrimeNormCharacterRestrictionStatement.{uE, uE, uE} →
  IsobaricWeakBaseChangeTowerStatement.{uF, uE, uE, uV, uW, uW} →
  IsobaricWeakBaseChangeTowerStatement.{uE, uE, uE, uW, uW, uW} →
  IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW} →
  CuspidalDeterminantTwistArithmeticComapStatement.{uE, uE} →
  CuspidalWeakBaseChangeNormTwistStatement.{uF, uE, uV, uW} →
  CuspidalSpectralAttachmentExistenceStatement.{uE, uV} →
  CuspidalSpectralAttachmentExistenceStatement.{uE, uW} →
  CuspidalSpectralArithmeticComapStatement.{uF, uE, uV} →
  CuspidalSpectralArithmeticComapStatement.{uE, uE, uW} →
  CyclicStableDescentTCStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified
