import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.CanonicalPairLFactor
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.PadicPairFactors

/-!
# Constructed equal-rank L-factors over p-adic fields

The proved equal-rank analytic theorem supplies the normalized polynomial and
rational-function unit for actual Whittaker-type representations. Genericity
supplies the full-type hypotheses in the canonical p-adic specialization.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Polynomial HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section SuppliedTopology

variable {n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Actual equal-rank zeta values have a normalized reciprocal-polynomial
generator for every compatible quotient measure. -/
theorem padicEqualRankNormalizedGeneratorExists :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (_hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        NormalizedGeneratorExists (equalRankZetaValues T.residueCardinality ψ
          (normalizedAbsoluteValue T) μ π σ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ μ hμ
  exact (equalRankAnalytic F T n).normalizedGeneratorExists ψ μ hμ V W π σ hπ hσ

/-- Existence at the constructed normalized quotient measure, with no measure
or analytic existence hypothesis. -/
theorem padicEqualRankNormalizedGeneratorExists_canonical :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (_hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      NormalizedGeneratorExists (equalRankZetaValues T.residueCardinality ψ
        (normalizedAbsoluteValue T) (unipotentQuotientHaar F.Carrier n) π σ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ
  exact padicEqualRankNormalizedGeneratorExists F T ψ π σ hπ hσ _
    (unipotentQuotientHaar_isCompatible F.Carrier n)

/-- The unique normalized L-polynomial of the actual equal-rank pair. -/
def padicEqualRankLPolynomial :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (_hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ℂ[X] := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ
  exact normalizedPolynomial _
    (padicEqualRankNormalizedGeneratorExists_canonical F T ψ π σ hπ hσ)

/-- The selected polynomial generates the Laurent span of the actual zeta
values at every compatible quotient measure. -/
theorem padicEqualRankLPolynomial_spec :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        IsEqualRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
          μ π σ (padicEqualRankLPolynomial F T ψ π σ hπ hσ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ μ hμ
  have hmeasure := unipotentQuotientHaar_unique F.Carrier n μ hμ
  subst μ
  exact normalizedPolynomial_spec _ _

/-- The constant coefficient of the selected polynomial is one. -/
@[simp] theorem padicEqualRankLPolynomial_coeff_zero :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      (padicEqualRankLPolynomial F T ψ π σ hπ hσ).coeff 0 = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ
  exact (padicEqualRankLPolynomial_spec F T ψ π σ hπ hσ _
    (unipotentQuotientHaar_isCompatible F.Carrier n)).1

/-- Any certified polynomial for a compatible measure is the selected one. -/
theorem padicEqualRankLPolynomial_eq :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier))
        (_hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
        {P : ℂ[X]},
        IsEqualRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) μ π σ P →
        padicEqualRankLPolynomial F T ψ π σ hπ hσ = P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ μ hμ P hP
  exact (padicEqualRankLPolynomial_spec F T ψ π σ hπ hσ μ hμ).unique hP

/-- The actual equal-rank L-factor as a unit in the rational functions in
`X = q^(-s)`, constructed from proved analytic existence. -/
def padicEqualRankLFactor :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (_hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      RationalFunctionsˣ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ
  exact equalRankLFactor T.residueCardinality ψ (normalizedAbsoluteValue T)
    (unipotentQuotientHaar F.Carrier n) π σ
    (padicEqualRankNormalizedGeneratorExists_canonical F T ψ π σ hπ hσ)

/-- The constructed L-factor is the reciprocal of the selected polynomial. -/
@[simp] theorem coe_padicEqualRankLFactor :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      (padicEqualRankLFactor F T ψ π σ hπ hσ : RationalFunctions) =
        (algebraMap ℂ[X] RationalFunctions
          (padicEqualRankLPolynomial F T ψ π σ hπ hσ))⁻¹ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ
  rfl

/-- Reciprocal characterization using any certified polynomial at any compatible
quotient measure. -/
theorem padicEqualRankLFactor_eq :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier))
        (_hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
        {P : ℂ[X]},
        IsEqualRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) μ π σ P →
        (padicEqualRankLFactor F T ψ π σ hπ hσ : RationalFunctions) =
          (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ μ hμ P hP
  rw [coe_padicEqualRankLFactor, padicEqualRankLPolynomial_eq F T ψ π σ hπ hσ μ hμ hP]

/-- The constructed polynomial also satisfies the unified pair relation. The
additive Haar measure does not enter the equal-rank integral. -/
theorem padicEqualRankLPolynomial_isPair :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (ν : AdditiveHaarMeasure F.Carrier)
        (μ : Measure (LeftUnipotentQuotient n F.Carrier))
        (_hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ),
        IsPairLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) μ ν π σ
          (padicEqualRankLPolynomial F T ψ π σ hπ hσ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ ν μ hμ
  exact isPairLPolynomial_self.mpr (padicEqualRankLPolynomial_spec F T ψ π σ hπ hσ μ hμ)

/-- The constructed factor agrees with the existing canonical pair constructor
for every proof of its existence and every additive Haar measure. -/
theorem padicEqualRankLFactor_eq_canonicalPairLFactor :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (ν : AdditiveHaarMeasure F.Carrier)
        (h : PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T)
          (unipotentQuotientHaar F.Carrier n) ν π σ),
        padicEqualRankLFactor F T ψ π σ hπ hσ = canonicalPairLFactor T n n ψ ν π σ h := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ π σ hπ hσ ν h
  apply Units.ext
  rw [coe_padicEqualRankLFactor,
    canonicalPairLFactor_eq T n n ψ ν π σ h _
      (padicEqualRankLPolynomial_isPair F T ψ π σ hπ hσ ν _
        (unipotentQuotientHaar_isCompatible F.Carrier n))]

end SuppliedTopology

section Generic

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : MeasurableSpace F.Carrier := borel F.Carrier

variable {n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ n π) (hσ : Whittaker.IsGeneric ψ n σ)

/-- The normalized polynomial of a generic equal-rank p-adic pair. Full type
and analytic existence are supplied by proved theorems. -/
def genericEqualRankLPolynomial : ℂ[X] :=
  padicEqualRankLPolynomial F F.canonicalTopologicalData ψ π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The L-factor of a generic equal-rank pair, with no supplied analytic
existence proof, functional or quotient measure. -/
def genericEqualRankLFactor : RationalFunctionsˣ :=
  padicEqualRankLFactor F F.canonicalTopologicalData ψ π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

@[simp] theorem coe_genericEqualRankLFactor :
    (genericEqualRankLFactor F ψ π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions (genericEqualRankLPolynomial F ψ π σ hπ hσ))⁻¹ :=
  rfl

@[simp] theorem genericEqualRankLPolynomial_coeff_zero :
    (genericEqualRankLPolynomial F ψ π σ hπ hσ).coeff 0 = 1 :=
  padicEqualRankLPolynomial_coeff_zero F F.canonicalTopologicalData ψ π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The constructed generic polynomial satisfies the existing p-adic pair
relation, including compatible-measure existence and every compatible measure. -/
theorem genericEqualRankLPolynomial_isPadic (ν : AdditiveHaarMeasure F.Carrier) :
    IsPadicPairLPolynomial F ψ ν π σ (genericEqualRankLPolynomial F ψ π σ hπ hσ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  constructor
  · exact ⟨inferInstance, unipotent_compatibleMeasureExists F.Carrier n⟩
  · intro _ μ hμ
    exact padicEqualRankLPolynomial_isPair F F.canonicalTopologicalData ψ π σ
      (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)
      ν μ hμ

/-- Every certified p-adic L-polynomial agrees with the constructed generic one. -/
theorem genericEqualRankLPolynomial_eq (ν : AdditiveHaarMeasure F.Carrier)
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν π σ P) :
    genericEqualRankLPolynomial F ψ π σ hπ hσ = P :=
  (genericEqualRankLPolynomial_isPadic F ψ π σ hπ hσ ν).unique hP

/-- Reciprocal characterization by any certified p-adic polynomial. -/
theorem genericEqualRankLFactor_eq (ν : AdditiveHaarMeasure F.Carrier)
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν π σ P) :
    (genericEqualRankLFactor F ψ π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  rw [coe_genericEqualRankLFactor, genericEqualRankLPolynomial_eq F ψ π σ hπ hσ ν hP]

end Generic

end Langlands.RankinSelberg
