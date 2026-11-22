import Langlands.Automorphic.Unramified.CyclicInductionSupercuspidalReduction
import Langlands.BaseChange.CompletionCommonSigmaLift
import Langlands.BaseChange.NormTwistFibreReduction
import Langlands.BaseChange.SigmaLiftGenericFibreStatement

/-! # Unique-place supercuspidality from the generic sigma-lift fibre -/

noncomputable section

universe uF uE uV uV' uW

set_option autoImplicit false

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality HarmonicAnalysis
open scoped NumberField FiniteExtension WithZero

section OrbitProduct

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]

local notation "Fv" => FiniteCompletion F v
local notation "Ew" => FiniteCompletion E w

local instance orbitProductValuativeRelBase : ValuativeRel Fv :=
  FiniteCompletion.valuativeRel v
local instance orbitProductValuativeRelTop : ValuativeRel Ew :=
  FiniteCompletion.valuativeRel w
local instance orbitProductLocalFieldBase : IsNonarchimedeanLocalField Fv :=
  FiniteCompletion.isNonarchimedeanLocalField v
local instance orbitProductLocalFieldTop : IsNonarchimedeanLocalField Ew :=
  FiniteCompletion.isNonarchimedeanLocalField w

set_option maxHeartbeats 800000 in
/-- A generic completion action with the full regular supercuspidal orbit
as its sigma-lift is supercuspidal, given cuspidal existence and the generic fibre. -/
theorem isSupercuspidal_of_generic_orbitProductLift_at_completion
    (hExist : CuspidalSigmaLiftExistenceStatement.{uF, uE, uV', uW})
    (hFibre : SigmaLiftGenericFibreStatement.{uF, uE, uV', uV, max uE uW})
    (σ : Ew ≃ₐ[Fv] Ew) (d : ℕ) (hcyc : IsCyclicAlgebra σ d)
    {r m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear (r + 1) Fv) V}
    {τ : Representation ℂ (GeneralLinear (m + 1) Ew) W}
    (hτ : GeneralLinear.IsSupercuspidal τ) (hτI : τ.IsIrreducible)
    (hstab : HasTrivialGaloisStabilizer Fv τ)
    (ψ : UnitaryAdditiveCharacter Fv) (hψ : Whittaker.IsGeneric ψ r π)
    (hOrbit : HasSigmaOrbitProductLift σ d π τ) :
    GeneralLinear.IsSupercuspidal π := by
  let : NontriviallyNormedField Fv :=
    Valued.toNontriviallyNormedField Fv (WithZero (Multiplicative ℤ))
  have : CharZero Fv := charZero_of_injective_algebraMap (algebraMap F Fv).injective
  have : IsModuleTopology Fv Ew := isModuleTopologyOfFiniteDimensional
  obtain ⟨hRank, hρ, hQ, B, b, hLiftQ⟩ := hOrbit
  obtain ⟨X, addX, modX, P, hP, V', addV', modV', π', hπ', hπ,
    A, A', c, c', hPI, hI', hSC', hSQ', hLift, hLift'⟩ :=
    exists_commonSigmaLift_of_orbitProductLift_at_completion v w hExist σ d hcyc
      (r + 1) m V W π τ hτ hτI hstab hRank hρ hQ B b hLiftQ
  let := addX
  let := modX
  let := addV'
  let := modV'
  obtain ⟨κ, hκ, ⟨e⟩⟩ := hFibre Fv Ew
    σ d r hcyc ψ π' hπ' π hπ P hP hI' hSQ' hψ hPI A' A c' c hLift' hLift
  exact (GeneralLinear.isSupercuspidal_iff_of_equiv e).mpr
    ((hκ.isSupercuspidal_twist_iff π').mpr hSC')

end OrbitProduct

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
  dsimp only
  intro σ d _ hcyc r m V _ _ W _ _ π τ hτ hstab hLocal
  obtain ⟨ψ, hψ⟩ := hLocal.2.2.1
  obtain ⟨_, hGenericτ⟩ := hLocal.2.2.2.2.2.1
  exact isSupercuspidal_of_generic_orbitProductLift_at_completion v w hExist hFibre
    σ d hcyc hτ hGenericτ.1 hstab ψ hψ hLocal.2.2.2.2.2.2.2

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
