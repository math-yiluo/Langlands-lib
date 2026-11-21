import Langlands.Automorphic.Unramified.CyclicInductionSupercuspidalReduction
import Langlands.BaseChange.CompletionCommonSigmaLift
import Langlands.BaseChange.NormTwistFibreReduction
import Langlands.BaseChange.SigmaLiftGenericFibreStatement

/-! # Unique-place supercuspidality from the generic sigma-lift fibre -/

noncomputable section

universe uF uE uV uV' uW

set_option autoImplicit false

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality
open scoped NumberField FiniteExtension WithZero

/-- Cuspidal sigma-lift existence and the generic fibre theorem imply the
local cyclic induction criterion at the actual finite completions. -/
def CyclicInductionSupercuspidalCompletionStatement : Prop :=
  CuspidalSigmaLiftExistenceStatement.{uF, uE, uV', uW} →
  SigmaLiftGenericFibreStatement.{uF, uE, uV', uV, max uE uW} →
  CyclicLocalInductionSupercuspidalAtCompletionStatement.{uF, uE, uV, uW}

set_option maxHeartbeats 800000 in
/-- The generic fibre comparison applies to the actual two actions at the
original rank of the finite completion. -/
theorem cyclicLocalInductionSupercuspidalAtCompletion_of_genericFibre :
    CyclicInductionSupercuspidalCompletionStatement.{uF, uE, uV, uV', uW} := by
  intro hExist hFibre F E _ _ _ _ _ v w _
  let := FiniteCompletion.valuativeRel v
  let := FiniteCompletion.valuativeRel w
  have := FiniteCompletion.isNonarchimedeanLocalField v
  have := FiniteCompletion.isNonarchimedeanLocalField w
  let : NontriviallyNormedField (FiniteCompletion F v) :=
    Valued.toNontriviallyNormedField (FiniteCompletion F v) (WithZero (Multiplicative ℤ))
  have : CharZero (FiniteCompletion F v) :=
    charZero_of_injective_algebraMap (algebraMap F (FiniteCompletion F v)).injective
  have : IsModuleTopology (FiniteCompletion F v) (FiniteCompletion E w) :=
    isModuleTopologyOfFiniteDimensional
  dsimp only
  intro σ d _ hcyc r m V _ _ W _ _ π τ hτ hstab hLocal
  obtain ⟨ψ, hψ⟩ := hLocal.2.2.1
  obtain ⟨_, hGenericτ⟩ := hLocal.2.2.2.2.2.1
  obtain ⟨hRank, hρ, hQ, B, b, hLiftQ⟩ := hLocal.2.2.2.2.2.2.2
  obtain ⟨X, addX, modX, P, hP, V', addV', modV', π', hπ', hπ,
    A, A', c, c', hPI, hI', hSC', hSQ', hLift, hLift'⟩ :=
    exists_commonSigmaLift_of_orbitProductLift_at_completion v w hExist σ d hcyc
      (r + 1) m V W π τ hτ hGenericτ.1 hstab hRank hρ hQ B b hLiftQ
  let := addX
  let := modX
  let := addV'
  let := modV'
  obtain ⟨κ, hκ, ⟨e⟩⟩ := hFibre (FiniteCompletion F v) (FiniteCompletion E w)
    σ d r hcyc ψ π' hπ' π hπ P hP hI' hSQ' hψ hPI A' A c' c hLift' hLift
  exact (GeneralLinear.isSupercuspidal_iff_of_equiv e).mpr
    ((hκ.isSupercuspidal_twist_iff π').mpr hSC')

end Langlands.BaseChange

namespace Langlands.Automorphic.Unramified

/-- The two local sigma-lift inputs suffice at the actual finite completion
in the unique-place global reduction. -/
theorem cyclicWeakInductionSupercuspidal_of_completionFibre
    (hMatch : CyclicInductionMatchingAtUniquePlaceStatement.{uF, uE, uV, uW})
    (hExist : BaseChange.CuspidalSigmaLiftExistenceStatement.{uF, uE, uF, uE})
    (hFibre : BaseChange.SigmaLiftGenericFibreStatement.{uF, uE, uF, uF, uE})
    (hRig : CuspidalEulerConstituentRecoveryStatement.{uF, uV}) :
    CyclicWeakInductionSupercuspidalStatement.{uF, uE, uV, uW} :=
  cyclicWeakInductionSupercuspidal_of_matching_at_completion hMatch
    (BaseChange.cyclicLocalInductionSupercuspidalAtCompletion_of_genericFibre hExist hFibre) hRig

/-- Specialize the finite-completion reduction to a totally complex base. -/
theorem cyclicWeakInductionSupercuspidalTC_of_completionFibre
    (hMatch : CyclicInductionMatchingAtUniquePlaceStatement.{uF, uE, uV, uW})
    (hExist : BaseChange.CuspidalSigmaLiftExistenceStatement.{uF, uE, uF, uE})
    (hFibre : BaseChange.SigmaLiftGenericFibreStatement.{uF, uE, uF, uF, uE})
    (hRig : CuspidalEulerConstituentRecoveryStatement.{uF, uV}) :
    CyclicWeakInductionSupercuspidalTCStatement.{uF, uE, uV, uW} :=
  cyclicWeakInductionSupercuspidalTC_of_unrestricted
    (cyclicWeakInductionSupercuspidal_of_completionFibre hMatch hExist hFibre hRig)

end Langlands.Automorphic.Unramified
