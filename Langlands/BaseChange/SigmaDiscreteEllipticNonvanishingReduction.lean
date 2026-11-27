import Langlands.BaseChange.ConcordantIntegralComparison
import Langlands.BaseChange.EllipticLocusClopen
import Langlands.BaseChange.OrdinaryWeylHaarLocalPushforwards
import Langlands.BaseChange.RegularSetOpenConull
import Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingStatement
import Langlands.BaseChange.SigmaDiscreteEllipticOrbitalTestStatement
import Langlands.BaseChange.TwistedCharacter.Saturation
import Langlands.BaseChange.TwistedCharacterLocalIntegrabilityStatement
import Langlands.BaseChange.TwistedCuspidalPseudoCoefficientExistenceStatement
import Langlands.BaseChange.TwistedTraceRegularNonvanishingReduction
import Langlands.BaseChange.TwistedWeylHaarLocalPushforwards

/-!
# Twisted characters of σ-discrete series on the σ-elliptic set: a reduction

For a cyclic field extension `E/F` of nonarchimedean local fields of characteristic zero, the
module proves that `SigmaDiscreteEllipticNonvanishingStatement` follows from two statements:

* `SigmaDiscreteEllipticOrbitalTestStatement`: a σ-discrete series `τ` of `GL_{r+1}(E)` has a
  test function whose σ-orbital integrals vanish off the σ-elliptic set and whose twisted trace
  is nonzero (a twisted pseudo-coefficient, Henniart–Lemaire 2011, II.5.14, Proposition 2 (2));
* `TwistedCharacterLocalIntegrabilityStatement`: twisted characters are given by locally
  integrable functions, locally constant near σ-regular elements (Clozel 1987, Theorem 1).

This is the argument of Arthur–Clozel 1989, Chapter 1, Lemma 2.12 (i), and of Henniart–Lemaire
2011, II.5.14, Corollaire 2. The module also proves the comparison of integrals of concordant
functions, `concordantIntegrableIntegralEquality`, from the proved local Haar pushforward and
open conull statements, and derives `SigmaDiscreteEllipticOrbitalTestStatement` from parts (a)
and (c) of `TwistedCuspidalPseudoCoefficientExistenceStatement`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis
open Langlands.QuotientIntegration Langlands.TraceFormula

universe u v uW

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- The comparison of the integrals of integrable concordant functions on `GL_n(E)` and
`GL_n(F)`: `ConcordantIntegralComparisonReductionStatement` applied to the proved local Haar
pushforward identities of the two Weyl maps and the proved openness and conullity of the
regular and σ-regular sets. -/
theorem concordantIntegrableIntegralEquality :
    ConcordantIntegrableIntegralEqualityStatement.{u, v} :=
  concordantIntegralComparisonReduction ordinaryWeylHaarLocalPushforwards
    twistedWeylHaarLocalPushforwards regularSemisimpleOpenConull sigmaRegularOpenConull

section Vanishing

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l n : ℕ}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The orbital integrals of the zero function vanish. -/
private theorem orbitalIntegral_zero_fun (γ : GeneralLinear n F)
    (ν : Measure (LeftQuotient (glCentralizer γ))) :
    orbitalIntegral γ ν (0 : GeneralLinear n F → ℂ) = 0 := by
  have h : twistedOrbitFunction (MonoidHom.id (GeneralLinear n F)) γ
      (0 : GeneralLinear n F → ℂ) = fun _ => 0 :=
    funext fun q => Quotient.inductionOn q fun _ => rfl
  rw [orbitalIntegral, twistedOrbitalIntegral, h, integral_zero]

/-- An integrable function on `GL_n(E)` whose σ-orbital integrals vanish at every σ-regular
element, for every right Haar measure on the σ-centralizer and every compatible quotient
measure, has integral zero: it is concordant with the zero function on `GL_n(F)`. -/
theorem integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero (hE : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure] {φ : GeneralLinear n E → ℂ}
    (hφ : Integrable φ μ)
    (h : ∀ δ : GeneralLinear n E, IsSigmaRegular σ l δ →
      ∀ (μδ : Measure (sigmaCentralizer σ n δ)) [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
        (νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ))),
        IsCompatible (sigmaCentralizer σ n δ) μ μδ νδ → sigmaOrbitalIntegral σ n δ νδ φ = 0) :
    ∫ g, φ g ∂μ = 0 := by
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let μF : Measure (GeneralLinear n F) := Measure.haar
  have hc : AreConcordant σ l μF μ φ 0 := by
    refine ⟨fun γ _ _ μγ _ _ νγ _ => orbitalIntegral_zero_fun γ νγ, ?_⟩
    intro δ γ hδγ hγ μδ _ _ μγ _ _ νδ νγ hcδ _ _
    rw [h δ ⟨γ, hδγ, hγ⟩ μδ νδ hcδ, orbitalIntegral_zero_fun]
  have heq := concordantIntegrableIntegralEquality F E σ l n hE μF μ φ 0 hφ
    (integrable_zero _ _ _) hc
  rw [heq]
  simp

end Vanishing

/-- Parts (a) and (c) of `TwistedCuspidalPseudoCoefficientExistenceStatement` give
`SigmaDiscreteEllipticOrbitalTestStatement`: a σ-discrete series is tempered, so it has a
central character; its twisted pseudo-coefficient has twisted trace `1` and σ-orbital
integrals vanishing off the σ-elliptic set. -/
theorem TwistedCuspidalPseudoCoefficientExistenceStatement.sigmaDiscreteEllipticOrbitalTest
    (h : TwistedCuspidalPseudoCoefficientExistenceStatement.{u, v, uW}) :
    SigmaDiscreteEllipticOrbitalTestStatement.{u, v, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l r hE
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
  let _ : MeasurableSpace (GeneralLinear (r + 1) E) := borel _
  have _ : BorelSpace (GeneralLinear (r + 1) E) := ⟨rfl⟩
  intro W _ _ τ hτ hdisc A μ _
  obtain ⟨χ, hχ⟩ : ∃ χ, HasCentralCharacterRep τ χ := by
    let _ : MeasurableSpace (GeneralLinear (r + 1) E ⧸
      Subgroup.center (GeneralLinear (r + 1) E)) := borel _
    have _ : BorelSpace (GeneralLinear (r + 1) E ⧸
      Subgroup.center (GeneralLinear (r + 1) E)) := ⟨rfl⟩
    obtain ⟨-, c, -⟩ := hdisc.2.2.1 (Measure.haarMeasure (Classical.arbitrary _))
    exact ⟨c.character, c.acts⟩
  obtain ⟨φ, ha, -, hc, -⟩ :=
    h F E σ l hE (r + 1) (Nat.succ_pos r) W τ hτ hdisc χ hχ A μ
  refine ⟨φ, hc, ?_⟩
  rw [ha.2.1]
  exact one_ne_zero

/-- `SigmaDiscreteEllipticNonvanishingStatement` follows from the existence of test functions
with σ-elliptic orbital integrals and nonzero twisted trace and from the local integrability
of twisted characters, at the same universe parameters (Arthur–Clozel 1989, Chapter 1,
Lemma 2.12 (i); Henniart–Lemaire 2011, II.5.14, Corollaire 2). -/
def SigmaDiscreteEllipticNonvanishingReductionStatement : Prop :=
  SigmaDiscreteEllipticOrbitalTestStatement.{u, v, uW} →
    TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} →
      SigmaDiscreteEllipticNonvanishingStatement.{u, v, uW}

/-- Proof of `SigmaDiscreteEllipticNonvanishingReductionStatement`. Let `φ₀` be a test
function with σ-orbital integrals vanishing off the σ-elliptic set and nonzero twisted trace,
and `Θ` the twisted character function. If `Θ` is nonzero at a σ-elliptic `δ`, the indicator
of a small compact open neighbourhood of `δ` in the open σ-elliptic set has nonzero twisted
trace. Otherwise `Θ` vanishes on the σ-elliptic set; since `Θ` is invariant under
σ-conjugation at σ-regular elements, every σ-orbital integral of `φ₀ Θ` at a σ-regular `δ` is
`Θ(δ)` times that of `φ₀`, hence zero, and the integral of `φ₀ Θ`, which is the twisted trace
of `φ₀`, vanishes. -/
theorem sigmaDiscreteEllipticNonvanishingReduction :
    SigmaDiscreteEllipticNonvanishingReductionStatement.{u, v, uW} := by
  intro htest hint F _ _ _ _ _ E _ _ _ _ _ σ l r hE
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
  let _ : MeasurableSpace (GeneralLinear (r + 1) E) := borel _
  have _ : BorelSpace (GeneralLinear (r + 1) E) := ⟨rfl⟩
  intro W _ _ τ hτ hdisc A μ _
  obtain ⟨φ₀, hvan, htr⟩ := htest F E σ l r hE τ hτ hdisc A μ
  obtain ⟨Θ, hΘ, hloc⟩ := hint F E σ l (r + 1) hE τ hτ hdisc.2.1 A
  have hA : ∀ g : GeneralLinear (r + 1) E, A.toLinearMap ∘ₗ τ g =
      τ ((entrywiseAut σ (r + 1)).toMonoidHom g) ∘ₗ A.toLinearMap :=
    fun g => A.comp_apply_eq g
  -- The character function is invariant under σ-conjugation at σ-regular elements.
  have hinv : ∀ δ : GeneralLinear (r + 1) E, IsSigmaRegular σ l δ →
      ∀ x : GeneralLinear (r + 1) E, Θ (x⁻¹ * δ * entrywiseAut σ (r + 1) x) = Θ δ := by
    intro δ hδ x
    have hδ' : IsSigmaRegular σ l (x⁻¹ * δ * entrywiseAut σ (r + 1) x) := by
      obtain ⟨γ, hδγ, hγ⟩ := hδ
      refine ⟨γ, ?_, hγ⟩
      simpa using hδγ.twistedConj hE.pow_eq_one x 1
    have h1 := (hΘ.hasTwistedCharacterValue (hloc δ hδ)).twistedConj hA x⁻¹
    have heq : x⁻¹ * δ * ((entrywiseAut σ (r + 1)).toMonoidHom x⁻¹)⁻¹ =
        x⁻¹ * δ * entrywiseAut σ (r + 1) x := by
      simp
    rw [heq] at h1
    exact (hΘ.hasTwistedCharacterValue (hloc _ hδ')).unique h1
  by_cases hex : ∃ δ : GeneralLinear (r + 1) E, IsSigmaElliptic σ l δ ∧ Θ δ ≠ 0
  · obtain ⟨δ, hδ, hΘδ⟩ := hex
    have hδr : IsSigmaRegular σ l δ := by
      obtain ⟨γ, hδγ, hγ⟩ := hδ
      exact ⟨γ, hδγ, hγ.isRegularSemisimple⟩
    obtain ⟨φ, hφR, hφ⟩ := exists_support_subset_ne_zero_of_hasLocalValue
      ((hΘ.hasTwistedCharacterValue (hloc δ hδr)) μ) hΘδ
      (isOpen_setOf_isSigmaElliptic hE (r + 1)) hδ
    exact ⟨φ, fun x hx => hφR hx, hφ⟩
  · push Not at hex
    exfalso
    apply htr
    have hint₁ : Integrable (fun g => φ₀ g * Θ g) μ := by
      have h₁ := ((hΘ μ).1).integrable_smul_left_of_hasCompactSupport φ₀.continuous
        φ₀.hasCompactSupport
      simpa only [smul_eq_mul] using h₁
    rw [(hΘ μ).2 φ₀]
    refine integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero hE μ hint₁ ?_
    intro δ hδ μδ _ _ νδ hc
    have hfun : twistedOrbitFunction (entrywiseAut σ (r + 1)) δ (fun g => φ₀ g * Θ g) =
        fun q => Θ δ * twistedOrbitFunction (entrywiseAut σ (r + 1)) δ (⇑φ₀) q := by
      funext q
      induction q using Quotient.inductionOn with
      | h x =>
        simp only [twistedOrbitFunction_mk]
        rw [hinv δ hδ x, mul_comm]
    rw [sigmaOrbitalIntegral, twistedOrbitalIntegral, hfun, integral_const_mul]
    by_cases hell : IsSigmaElliptic σ l δ
    · rw [hex δ hell, zero_mul]
    · have h₀ := hvan δ hδ hell μδ νδ hc
      rw [sigmaOrbitalIntegral, twistedOrbitalIntegral] at h₀
      rw [h₀, mul_zero]

end Langlands.BaseChange
