import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityLandauReduction
import Langlands.Global.Factors.CuspidalPairPoleFiniteEuler
import Langlands.Global.Factors.CuspidalPairPoleTCReduction
import Langlands.Global.Factors.CuspidalSelfPairContinuationProof

set_option autoImplicit false

universe uF uV

namespace Langlands.Automorphic.Unramified

open NumberField Langlands.Global
open CuspidalWhittaker (adelicCharacter adelicCharacter_algebraMap
  continuous_adelicCharacter exists_adelicCharacter_ne_one)
open CuspidalPairLandauOrders (landauAsymptoticsReduction)
open CuspidalPairPartialContinuation (CompletedPoleProfileAt
  exists_partialPairL_of_completedPoleProfile)
open CuspidalPairPoles (CuspidalPairNormalizedContinuationTCAt
  archimedeanPairProduct_eq_complex_of_totallyComplex standardFinitePairLChoice)
open LocalFactor.Archimedean (RealBlock)

private theorem completedPoleProfileAt_of_normalizedContinuationTC
    {F : Type uF} [Field F] [NumberField F] [IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)]
    (continuation : CuspidalPairNormalizedContinuationTCAt.{uF, uV} F) :
    CompletedPoleProfileAt.{uF, uV} F := by
  classical
  intro r t T T' hT hT' P P' h h'
  let ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F) :=
    ⟨adelicCharacter F, continuous_adelicCharacter F, by
      obtain ⟨x, hx⟩ := exists_adelicCharacter_ne_one F
      intro heq
      exact hx (by simp [heq])⟩
  let _ : IsEmpty {v : NumberField.InfinitePlace F // v.IsReal} :=
    ⟨fun v => NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex v.1) v.2⟩
  let dR : {v : NumberField.InfinitePlace F // v.IsReal} → List RealBlock :=
    fun v => isEmptyElim v
  choose dC hdC using (cuspidalArchimedeanParameterExistenceTC F r T).2
  choose dC' hdC' using (cuspidalArchimedeanParameterExistenceTC F t T').2
  let c := standardFinitePairLChoice (P := P) (P' := P') (h := h) (h' := h')
  obtain ⟨Λ, hCompleted, hPole, _⟩ :=
    continuation ψ (adelicCharacter_algebraMap F) r t T T' hT hT' P P' h h' c dC dC' hdC hdC'
  refine ⟨c, dR, dR, dC, dC', (fun v => isEmptyElim v), (fun v => isEmptyElim v),
    hdC, hdC', Λ, ?_, hPole⟩
  rw [archimedeanPairProduct_eq_complex_of_totallyComplex]
  exact hCompleted

/-- Completed simple pole profiles over totally complex fields give all three
cuspidal spectral rigidity conclusions at the two independent universes. -/
def CuspidalSpectralRigidityTCPoleProfileReductionStatement : Prop :=
  (∀ (F : Type uF) [Field F] [NumberField F] [IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)], CompletedPoleProfileAt.{uF, uV} F) →
  CuspidalSpectralRigidityTCStatement.{uF, uV}

theorem cuspidalSpectralRigidityTCPoleProfileReduction :
    CuspidalSpectralRigidityTCPoleProfileReductionStatement.{uF, uV} := by
  intro poleProfile
  have convergence : CuspidalPairAbsoluteConvergenceStatement.{uF, uV} :=
    cuspidalPairAbsoluteConvergence_of_selfPairContinuation cuspidalSelfPairContinuation
  have independence := cuspidalPowerTraceIndependenceTC_of_pairLogAsymptotics convergence
    (fun F _ _ _ _ => landauAsymptoticsReduction convergence F
      (exists_partialPairL_of_completedPoleProfile (poleProfile F) convergence))
  have recovery : CuspidalPowerTraceConstituentRecoveryTCStatement.{uF, uV} :=
    fun F _ _ _ _ => cuspidalPowerTraceConstituentRecoveryAt_of_independenceAt (independence F)
  exact ⟨independence, recovery,
    fun F _ _ _ _ => cuspidalEulerConstituentRecoveryAt_of_powerTraceRecoveryAt (recovery F)⟩

/-- The normalized complex-place continuation supplies the completed pole profile
used to recover the cuspidal constituents. -/
theorem cuspidalSpectralRigidityTC_of_normalizedContinuation
    (continuation : ∀ (F : Type uF) [Field F] [NumberField F] [IsTotallyComplex F]
      [CompactSpace (AdeleQuotient F)], CuspidalPairNormalizedContinuationTCAt.{uF, uV} F) :
    CuspidalSpectralRigidityTCStatement.{uF, uV} :=
  cuspidalSpectralRigidityTCPoleProfileReduction
    (fun F _ _ _ _ => completedPoleProfileAt_of_normalizedContinuationTC (continuation F))

end Langlands.Automorphic.Unramified
