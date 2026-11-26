import Langlands.BaseChange.SigmaLiftCharacterIdentity.Forward
import Langlands.BaseChange.SigmaLiftCharacterIdentityReverse
import Langlands.BaseChange.RegularTransfer
import Langlands.BaseChange.CyclicNormLemma
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct

/-! # The σ-lift character identity from integral comparison and local integrability -/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- The integral comparison for integrable concordant functions contains the one for
concordant test functions. -/
theorem concordantIntegralEquality_of_integrable.{u, v}
    (h : ConcordantIntegrableIntegralEqualityStatement.{u, v}) :
    ConcordantIntegralEqualityStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE _ _ _ _ μF _ μE _ φ f hφf
  exact h F E σ l n hE μF μE φ f (SchwartzBruhat.integrable φ μE)
    (SchwartzBruhat.integrable f μF) hφf

/-- Local integrability of twisted characters in degree one, for the identity automorphism
and the identity intertwiner, is local integrability of ordinary characters. -/
theorem characterLocalIntegrability_of_twisted.{u, uV}
    (h : TwistedCharacterLocalIntegrabilityStatement.{u, u, uV}) :
    CharacterLocalIntegrabilityStatement.{u, uV} := by
  intro F _ _ _ _ _ n
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  intro V _ _ ρ hρ hirr
  let A : SigmaIntertwiner (1 : F ≃ₐ[F] F) n ρ :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => by
      ext v
      simp [entrywiseAut_one_apply])
  obtain ⟨Θ, hΘ, hloc⟩ := h F F 1 1 n (isCyclicAlgebra_one (F := F)) ρ hρ hirr A
  refine ⟨Θ, isTwistedCharacterFunction_one_iff.1 hΘ, fun γ hγ => hloc γ ?_⟩
  refine ⟨γ, ⟨1, ?_⟩, hγ⟩
  have hbase : baseChange F F n γ = γ := by
    apply Units.ext
    ext i j
    simp [baseChange_apply_apply]
  rw [cyclicNorm_succ, cyclicNorm_zero, pow_zero, entrywiseAut_one_apply, hbase]
  simp

/-- The σ-lift character identity follows from the comparison of integrals of
integrable concordant functions and from local integrability of twisted characters, in
the two universe instances used for `GL_n(F)` and for `GL_n(E)`. -/
def SigmaLiftCharacterIdentityReductionStatement.{u, v, uV, uW} : Prop :=
  ConcordantIntegrableIntegralEqualityStatement.{u, v} →
  TwistedCharacterLocalIntegrabilityStatement.{u, u, uV} →
  TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} →
  SigmaLiftCharacterIdentityStatement.{u, v, uV, uW}

theorem sigmaLiftCharacterIdentityReduction.{u, v, uV, uW} :
    SigmaLiftCharacterIdentityReductionStatement.{u, v, uV, uW} := by
  intro hintegral hordinary htwisted F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : Module.Finite F E := hE.1
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro V _ _ W _ _ π hπ τ hτ hπirr hτirr A c
  exact ⟨sigmaLiftCharacterIdentityForward hordinary.regularValues htwisted.regularValues
      regularTransfer (concordantIntegralEquality_of_integrable hintegral)
      (SigmaLiftCharacterIdentity.sigmaRegularOpen_of_cyclicNormLemma cyclicNormLemma)
      F E σ l n hE π hπ τ hτ hπirr hτirr A c,
    sigmaLiftCharacterIdentityReverse hintegral
      (characterLocalIntegrability_of_twisted hordinary) htwisted
      F E σ l n hE π hπ τ hτ hπirr hτirr A c⟩

end Langlands.BaseChange
