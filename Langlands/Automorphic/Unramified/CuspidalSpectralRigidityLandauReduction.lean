import Langlands.Automorphic.Unramified.CuspidalPowerTraceIndependenceReduction
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityReduction
import Langlands.Global.Factors.CuspidalPairLandauOrders

/-! # Cuspidal spectral rigidity from completed pair poles and absolute convergence -/

set_option autoImplicit false

universe uF uV

namespace Langlands.Automorphic.Unramified

open Langlands.Global
open CuspidalPairLandauOrders (landauAsymptoticsReduction)
open CuspidalPairPartialContinuation (partialPairContinuationReduction)

/-- Given absolute convergence, completed pair poles imply cuspidal spectral
rigidity. The totally complex pole statement suffices for the totally complex
rigidity proposition. -/
def CuspidalSpectralRigidityLandauReductionStatement : Prop :=
  CuspidalPairAbsoluteConvergenceStatement.{uF, uV} →
    ((CuspidalPairPoleStatement.{uF, uV} → CuspidalSpectralRigidityStatement.{uF, uV}) ∧
      (CuspidalPairPoleTCStatement.{uF, uV} → CuspidalSpectralRigidityTCStatement.{uF, uV}))

theorem cuspidalSpectralRigidityLandauReduction :
    CuspidalSpectralRigidityLandauReductionStatement.{uF, uV} := by
  intro hconv
  obtain ⟨hpartial, hpartialTC⟩ := partialPairContinuationReduction hconv
  have hasymptotics := landauAsymptoticsReduction hconv
  constructor
  · intro hpole
    exact cuspidalSpectralRigidity_of_independence
      (cuspidalPowerTraceIndependence_of_pairLogAsymptotics hconv
        (fun F _ _ _ => hasymptotics F (hpartial hpole F)))
  · intro hpole
    have hind := cuspidalPowerTraceIndependenceTC_of_pairLogAsymptotics hconv
      (fun F _ _ _ _ => hasymptotics F (hpartialTC hpole F))
    have hrec : CuspidalPowerTraceConstituentRecoveryTCStatement.{uF, uV} :=
      fun F _ _ _ _ => cuspidalPowerTraceConstituentRecoveryAt_of_independenceAt (hind F)
    exact ⟨hind, hrec,
      fun F _ _ _ _ => cuspidalEulerConstituentRecoveryAt_of_powerTraceRecoveryAt (hrec F)⟩

end Langlands.Automorphic.Unramified
