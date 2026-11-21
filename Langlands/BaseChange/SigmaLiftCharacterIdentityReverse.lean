import Langlands.BaseChange.CharacterLocalIntegrabilityStatement
import Langlands.BaseChange.CharacterLocalValueConjugation
import Langlands.BaseChange.ConcordantIntegrableIntegralEqualityStatement
import Langlands.BaseChange.TwistedCharacterLocalIntegrabilityStatement
import Langlands.BaseChange.WeightedConcordance

/-! # The reverse direction of the σ-lift character identity -/

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis Langlands.JacquetLanglands

/-- The Shintani identity implies the σ-lift identity given the integral comparison
for concordant integrable functions and the two character integrability statements. -/
def SigmaLiftCharacterIdentityReverseStatement.{u, v, uV, uW} : Prop :=
  ConcordantIntegrableIntegralEqualityStatement.{u, v} →
  CharacterLocalIntegrabilityStatement.{u, uV} →
  TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      π.IsIrreducible → τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ) (c : ℂ),
        IsShintaniLift σ l π hπ τ hτ A c → IsSigmaLift σ l π hπ τ hτ A c

universe u v uV uW

private theorem isRegularSemisimple_conjugate {F : Type u} [Field F] {n : ℕ}
    {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) (x : GeneralLinear n F) :
    IsRegularSemisimple (x⁻¹ * γ * x) := by
  unfold IsRegularSemisimple at hγ ⊢
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  exact hγ

set_option maxHeartbeats 600000 in
theorem sigmaLiftCharacterIdentityReverse :
    SigmaLiftCharacterIdentityReverseStatement.{u, v, uV, uW} := by
  intro hIntegral hOrdinary hTwisted F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : Module.Finite F E := hE.1
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro V _ _ W _ _ π hπ τ hτ hπirr hτirr A c hShintani
  obtain ⟨θ, hθ, hθloc⟩ := hOrdinary F n π hπ hπirr
  obtain ⟨Θ, hΘ, hΘloc⟩ := hTwisted F E σ l n hE τ hτ hτirr A
  have hvalue γ (hγ : IsRegularSemisimple γ) : HasCharacterValue π hπ γ (θ γ) :=
    hθ.hasCharacterValue (hθloc γ hγ)
  have hOrdWeight γ (hγ : IsRegularSemisimple γ) (x : GeneralLinear n F) :
      c * θ (x⁻¹ * γ * x) = c * θ γ := by
    have hconj := isRegularSemisimple_conjugate hγ x
    rw [(hvalue _ hconj).unique ((hvalue γ hγ).conjugate x)]
  have hTwistWeight δ γ (hassoc : IsNormAssociated σ l δ γ)
      (hγ : IsRegularSemisimple γ) (x : GeneralLinear n E) :
      Θ (x⁻¹ * δ * entrywiseAut σ n x) = c * θ γ := by
    let δ' := x⁻¹ * δ * entrywiseAut σ n x
    have hassoc' : IsNormAssociated σ l δ' γ := by
      simpa [δ'] using hassoc.twistedConj hE.pow_eq_one x 1
    obtain ⟨a, ha, htw⟩ := hShintani.2 δ' γ hassoc' hγ
    have hval' := hΘ.hasTwistedCharacterValue (hΘloc δ' ⟨γ, hassoc', hγ⟩)
    rw [hval'.unique htw, ha.unique (hvalue γ hγ)]
  refine ⟨hShintani.1, ?_⟩
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let _ : MeasurableSpace (GeneralLinear n E) := borel _
  have _ : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro μF _ μE _ φ f hconcord
  obtain ⟨hθint, hθdist⟩ := hθ μF
  obtain ⟨hΘint, hΘdist⟩ := hΘ μE
  have hφΘ : Integrable (fun x => φ x * Θ x) μE :=
    hΘint.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  have hfθ : Integrable (fun x => f x * (c * θ x)) μF :=
    (hθint.smul c).integrable_smul_left_of_hasCompactSupport f.continuous f.hasCompactSupport
  calc
    twistedDistribution μE τ hτ A.toLinearMap φ = ∫ x, φ x * Θ x ∂μE := hΘdist φ
    _ = ∫ x, f x * (c * θ x) ∂μF :=
      hIntegral F E σ l n hE μF μE _ _ hφΘ hfθ
        (hconcord.mul_of_orbitValues Θ (fun x => c * θ x) hOrdWeight hTwistWeight)
    _ = c * ∫ x, f x * θ x ∂μF := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_left_comm _ _ _)
    _ = c * Character.distribution μF π hπ f := by rw [hθdist]

end Langlands.BaseChange
