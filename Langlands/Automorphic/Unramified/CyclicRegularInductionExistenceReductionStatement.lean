import Langlands.Automorphic.Unramified.CuspidalSpectralAttachmentExistenceStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement
import Langlands.Automorphic.Unramified.CyclicOrbitInductionComparisonStatement
import Langlands.Automorphic.Unramified.CyclicPrimeRegularOrbitRealizationStatement
import Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangePairMultiplicityStatement
import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeTransportStatement
import Langlands.Automorphic.Unramified.WeakInductionTransitivityStatement

/-! # Building cyclic regular induction from prime orbit realizations -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

/-- The prime orbit realization, the weak-transfer comparisons and Euler constituent recovery
give the actual cuspidal induction of a regular upper cusp in any cyclic degree. -/
def CyclicRegularInductionExistenceReductionStatement : Prop :=
  CyclicPrimeRegularOrbitRealizationStatement.{uF, uE, uV, uW} →
  CyclicPrimeRegularOrbitRealizationStatement.{uE, uE, uW, uW} →
  CyclicWeakBaseChangePairMultiplicityStatement.{uF, uE, uV, uW} →
  CyclicWeakBaseChangePairMultiplicityStatement.{uE, uE, uW, uW} →
  CyclicOrbitBaseChangeWeakInductionStatement.{uF, uE, uV, uW} →
  CyclicOrbitBaseChangeWeakInductionStatement.{uE, uE, uW, uW} →
  IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW} →
  CuspidalEulerConstituentRecoveryStatement.{uE, uW} →
  WeakInductionTransitivityStatement.{uF, uE, uE, uV, uW, uW} →
  CuspidalSpectralAttachmentExistenceStatement.{uE, uV} →
  CuspidalSpectralAttachmentExistenceStatement.{uE, uW} →
    CyclicRegularInductionExistenceStatement.{uF, uE, uV, uW}

/-- The same induction over a totally complex base, using the corresponding prime orbit
realization, pair comparison and Euler constituent recovery. -/
def CyclicRegularInductionExistenceReductionTCStatement : Prop :=
  CyclicPrimeRegularOrbitRealizationTCStatement.{uF, uE, uV, uW} →
  CyclicPrimeRegularOrbitRealizationTCStatement.{uE, uE, uW, uW} →
  CyclicWeakBaseChangePairMultiplicityTCStatement.{uF, uE, uV, uW} →
  CyclicWeakBaseChangePairMultiplicityTCStatement.{uE, uE, uW, uW} →
  CyclicOrbitBaseChangeWeakInductionStatement.{uF, uE, uV, uW} →
  CyclicOrbitBaseChangeWeakInductionStatement.{uE, uE, uW, uW} →
  IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW} →
  CuspidalEulerConstituentRecoveryTCStatement.{uE, uW} →
  WeakInductionTransitivityStatement.{uF, uE, uE, uV, uW, uW} →
  CuspidalSpectralAttachmentExistenceStatement.{uE, uV} →
  CuspidalSpectralAttachmentExistenceStatement.{uE, uW} →
    CyclicRegularInductionExistenceTCStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified
