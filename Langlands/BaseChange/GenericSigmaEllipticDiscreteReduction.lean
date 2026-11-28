import Langlands.BaseChange.EllipticLocusClopen
import Langlands.BaseChange.GenericSigmaEllipticDiscreteStatement
import Langlands.BaseChange.GenericSigmaNoninducedTemperedStatement
import Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingReduction
import Langlands.BaseChange.SigmaInducedEllipticVanishingStatement
import Langlands.BaseChange.TwistedCharacterLocalIntegrabilityStatement
import Langlands.BaseChange.TwistedTraceRegularNonvanishingReduction

/-!
# Generic σ-elliptic representations are σ-discrete: a reduction

For a cyclic field extension `E/F` of nonarchimedean local fields of characteristic zero, the
module proves that `GenericSigmaEllipticDiscreteStatement` follows from three statements:

* `TwistedCharacterLocalIntegrabilityStatement`: twisted characters are given by locally
  integrable functions, locally constant near σ-regular elements (Clozel 1987, Theorem 1);
* `SigmaInducedEllipticVanishingStatement`: the twisted trace of an irreducible representation
  isomorphic to the smooth induction of a σ-stable representation of a proper standard Levi
  subgroup vanishes on test functions supported in the σ-elliptic set (Henniart–Lemaire 2011,
  II.4.5);
* `GenericSigmaNoninducedTemperedStatement`: a generic σ-stable representation with unitary
  central character that is not such an induction is tempered.

This is the argument of Henniart–Lemaire 2011, II.5.8, Lemme, with II.5.15, Proposition 1, and
of Arthur–Clozel 1989, Chapter 1, Lemma 2.11, with the twisted Weyl integration formula
replaced by the comparison of integrals of concordant functions
(`integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero`). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis Langlands.GeneralLinear
open Langlands.QuotientIntegration Langlands.TraceFormula

universe u v uW

/-- `GenericSigmaEllipticDiscreteStatement` follows from the local integrability of twisted
characters, the vanishing of twisted traces of σ-stable proper inductions on the σ-elliptic set,
and the temperedness of generic σ-stable representations with unitary central character that
are not σ-stable proper inductions, at the same universe parameters (Henniart–Lemaire 2011,
II.5.8, Lemme, and II.5.15, Proposition 1; Arthur–Clozel 1989, Chapter 1, Lemma 2.11). -/
def GenericSigmaEllipticDiscreteReductionStatement : Prop :=
  TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} →
    SigmaInducedEllipticVanishingStatement.{u, v, uW} →
      GenericSigmaNoninducedTemperedStatement.{u, v, uW} →
        GenericSigmaEllipticDiscreteStatement.{u, v, uW}

/-- Proof of `GenericSigmaEllipticDiscreteReductionStatement`. Irreducibility and admissibility
come from genericity and σ-stability from `A`. If `τ` were isomorphic to the smooth induction of
a σ-stable representation of a proper standard Levi subgroup, its twisted trace would vanish on
every test function supported in the σ-elliptic set. The twisted character function `Θ` is
locally constant at σ-regular elements, so it would vanish on the open σ-elliptic set; since
`Θ` is invariant under σ-conjugation at σ-regular elements, every σ-orbital integral of
`φ Θ` would vanish (at σ-elliptic elements because `Θ` is zero there, elsewhere because those of
`φ` are), and the twisted trace of `φ`, the integral of `φ Θ`, would be zero. Temperedness then
follows from the third statement. -/
theorem genericSigmaEllipticDiscreteReduction :
    GenericSigmaEllipticDiscreteReductionStatement.{u, v, uW} := by
  intro hint hvan htemp F _ _ _ _ _ E _ _ _ _ _ σ l r hE
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
  let _ : MeasurableSpace (GeneralLinear (r + 1) E) := borel _
  have _ : BorelSpace (GeneralLinear (r + 1) E) := ⟨rfl⟩
  intro W _ _ τ hτ ψ hgen χ hχ hunit A μ _ φ₀ hvan₀ htr
  have hirr : τ.IsIrreducible := hgen.1
  obtain ⟨Θ, hΘ, hloc⟩ := hint F E σ l (r + 1) hE τ hτ hirr A
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
  -- If the twisted trace vanishes on the σ-elliptic set, it vanishes at `φ₀`.
  have hzero : (∀ φ : SchwartzBruhat (GeneralLinear (r + 1) E),
      IsSigmaEllipticSupported σ l ⇑φ → twistedDistribution μ τ hτ A.toLinearMap φ = 0) →
      twistedDistribution μ τ hτ A.toLinearMap φ₀ = 0 := by
    intro hell
    have hex : ∀ δ : GeneralLinear (r + 1) E, IsSigmaElliptic σ l δ → Θ δ = 0 := by
      intro δ hδ
      by_contra hΘδ
      have hδr : IsSigmaRegular σ l δ := by
        obtain ⟨γ, hδγ, hγ⟩ := hδ
        exact ⟨γ, hδγ, hγ.isRegularSemisimple⟩
      obtain ⟨φ, hφR, hφ⟩ := exists_support_subset_ne_zero_of_hasLocalValue
        ((hΘ.hasTwistedCharacterValue (hloc δ hδr)) μ) hΘδ
        (isOpen_setOf_isSigmaElliptic hE (r + 1)) hδ
      exact hφ (hell φ fun x hx => hφR hx)
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
    by_cases hell' : IsSigmaElliptic σ l δ
    · rw [hex δ hell', zero_mul]
    · have h₀ := hvan₀ δ hδ hell' μδ νδ hc
      rw [sigmaOrbitalIntegral, twistedOrbitalIntegral] at h₀
      rw [h₀, mul_zero]
  -- `τ` is not a σ-stable proper induction.
  have hnind : ∀ B : BlockShape (r + 1), 2 ≤ B.length →
      ∀ (X : Type uW) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X),
        IsSmooth Ξ → IsLeviSigmaStable σ B Ξ →
          IsEmpty (τ.Equiv
            (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))) := by
    intro B hB X _ _ Ξ hΞ hΞσ
    refine ⟨fun e => htr (hzero fun φ hφ => ?_)⟩
    exact hvan F E σ l (r + 1) hE τ hτ hirr B hB X Ξ hΞ hΞσ ⟨e⟩ A μ φ hφ
  exact ⟨hτ, hirr, htemp F E σ l r hE τ hτ ψ hgen χ hχ hunit ⟨A⟩ hnind, ⟨A⟩, hnind⟩

end Langlands.BaseChange
