import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.HarmonicAnalysis.Conductor

/-!
# Pair factors after highly ramified twists

Jacquet and Shalika 1985. Proposition 4.1 (printed page 326): two irreducible
generic representations `π₁, π₂` of `GL_r(F)` with the same central character
have the same gamma factor of pairs against a fixed irreducible generic
representation `σ` after twisting by any character of sufficiently large
conductor. Proposition 5.1 (printed page 331): after such a twist the L-factor
of a pair is `1`. The introduction (printed page 319) states the analogous
property for the epsilon factors of pairs, which follows from the two
propositions. The factors are the relations `IsPadicSymmetricGammaFactor`,
`IsPadicSymmetricEpsilonFactor` and `IsPadicSymmetricLPolynomial` with the
self-dual measure, which cover both rank orders; agreement means one common
factor value.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- Two actual representations of `GL_(r+1)(F)` have the same central character:
some character `ω` of `Fˣ` gives the action of every scalar matrix on both. -/
def SameGLCentralCharacter (F : PadicField.{uF} p) {r : ℕ}
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂) : Prop :=
  ∃ ω : F.Carrierˣ →* ℂˣ, Classification.HasGLCentralCharacter F.Carrier (r + 1) π₁ ω ∧
    Classification.HasGLCentralCharacter F.Carrier (r + 1) π₂ ω

/-- Jacquet and Shalika 1985, Proposition 4.1 (printed page 326). Let `ψ` have
conductor exponent `0` (largest trivial ideal `O`), let `π₁, π₂` be irreducible
admissible generic representations of `GL_(r+1)(F)` with the same central
character, and `σ` one of `GL_(t+1)(F)`, of any ranks. Then there is `A` such
that for every quasicharacter `χ` of `Fˣ` with conductor exponent `a ≥ A` the
twists `π₁ ⊗ (χ ∘ det)` and `π₂ ⊗ (χ ∘ det)` have one common gamma factor
against `σ`. -/
def HighlyRamifiedGammaStabilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ (r t : ℕ),
    ∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
      (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
      (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₁) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₂) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ) →
    SameGLCentralCharacter F π₁ π₂ →
    ∃ A : ℕ, ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∃ G : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ G ∧
        IsPadicSymmetricGammaFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ G

/-- The epsilon-factor form of the stability property, stated for pairs in
Jacquet and Shalika 1985, introduction (printed page 319), and proved there by
Propositions 4.1 and 5.1 (printed pages 326 and 331), with the same hypotheses
as `HighlyRamifiedGammaStabilityStatement`:
after twisting by any quasicharacter of conductor exponent `a ≥ A`, the twists of
`π₁` and `π₂` have one common epsilon factor against `σ`. -/
def HighlyRamifiedEpsilonStabilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ (r t : ℕ),
    ∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
      (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
      (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₁) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π₂) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ) →
    SameGLCentralCharacter F π₁ π₂ →
    ∃ A : ℕ, ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∃ e : ℂˣ × ℤ,
        IsPadicSymmetricEpsilonFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ e ∧
        IsPadicSymmetricEpsilonFactor F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ e

/-- Jacquet and Shalika 1985, Proposition 5.1 (printed page 331). Let `ψ` have
conductor exponent `0`, and let `π` and `σ` be irreducible admissible generic
representations of `GL_(r+1)(F)` and `GL_(t+1)(F)`, of any ranks. Then there
is `A` such that for every quasicharacter `χ` of `Fˣ` with conductor exponent
`a ≥ A` the L-polynomial of the pair `(π ⊗ (χ ∘ det), σ)` is `1`, that is,
`L(s, (π ⊗ χ) × σ) = 1`. -/
def HighlyRamifiedLVanishingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ (r t : ℕ),
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π) →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ) →
    ∃ A : ℕ, ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ 1

/-- The three statements of Jacquet and Shalika 1985 for generic pairs: gamma
stability, L-vanishing and epsilon stability. -/
def HighlyRamifiedStabilityStatement : Prop :=
  HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} ∧
    HighlyRamifiedLVanishingStatement.{uF, uV, uW} ∧
    HighlyRamifiedEpsilonStabilityStatement.{uF, uV, uW}

end Langlands.RankinSelberg
