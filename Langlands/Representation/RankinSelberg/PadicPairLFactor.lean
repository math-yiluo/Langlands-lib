import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankCommonGeneratorProof
import Langlands.Representation.RankinSelberg.CanonicalPairLFactor
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.PadicPairFactors

/-!
# Constructed p-adic pair L-factors for equal and larger-first ranks

The published equal/unequal analytic and unequal common-generator theorems
supply polynomial existence for full Whittaker-type pairs. The resulting
polynomial and rational-function unit have no analytic or quotient-measure
premise and satisfy the existing pair relations at every compatible measure.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Polynomial HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section SuppliedTopology

variable (T : F.TopologicalData) {n r : ℕ}
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (hnr : n ≤ r)

include hnr

/-- Polynomial existence from the published analytics and common-generator theorem. -/
theorem padicPairLPolynomialExists :
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
      (ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (_hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
      (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier))
        (_hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ),
        PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T) μ ν π σ := by
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
  intro ψ ν π σ hπ hσ μ hμ
  rcases hnr.eq_or_lt with h | h
  · subst r
    exact (equalRankAnalytic.{uF,uV,uW} F T n).pairLPolynomialExists
      ψ μ hμ ν V W π σ hπ hσ
  · exact (unequalRankCommonGenerator.{uF,uV,uW} F T n r).pairLPolynomialExists
      (fun j k _ => unequalRankAnalytic.{uF,uV,uW} F T n j k) h
      ψ μ hμ ν V W π σ hπ hσ

/-- Existence at the constructed normalized quotient measure. -/
theorem padicPairLPolynomialExists_canonical :
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
      (ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (_hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
      (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar F.Carrier n) ν π σ := by
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
  intro ψ ν π σ hπ hσ
  exact padicPairLPolynomialExists F T hnr ψ ν π σ hπ hσ _
    (unipotentQuotientHaar_isCompatible F.Carrier n)

/-- The normalized pair polynomial selected from proved existence. -/
def padicPairLPolynomial :
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
      (_ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (_hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
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
  intro ψ ν π σ hπ hσ
  exact pairLPolynomial
    (padicPairLPolynomialExists_canonical F T hnr ψ ν π σ hπ hσ)

/-- The selected polynomial is certified for every block and every quotient
measure compatible with the fixed ambient and subgroup Haar measures. -/
theorem padicPairLPolynomial_spec :
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
      (ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier))
        (_hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ),
        IsPairLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
          μ ν π σ (padicPairLPolynomial F T hnr ψ ν π σ hπ hσ) := by
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
  intro ψ ν π σ hπ hσ μ hμ
  have hm := unipotentQuotientHaar_unique F.Carrier n μ hμ
  subst μ
  exact pairLPolynomial_spec _

/-- The constant coefficient is one. -/
@[simp] theorem padicPairLPolynomial_coeff_zero :
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
      (ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      (padicPairLPolynomial F T hnr ψ ν π σ hπ hσ).coeff 0 = 1 := by
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
  intro ψ ν π σ hπ hσ
  exact (padicPairLPolynomial_spec F T hnr ψ ν π σ hπ hσ _
    (unipotentQuotientHaar_isCompatible F.Carrier n)).coeff_zero

/-- Uniqueness against a certified polynomial at any compatible quotient measure. -/
theorem padicPairLPolynomial_eq :
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
      (ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier))
        (_hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ),
      ∀ {P : ℂ[X]},
        IsPairLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) μ ν π σ P →
        padicPairLPolynomial F T hnr ψ ν π σ hπ hσ = P := by
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
  intro ψ ν π σ hπ hσ μ hμ P hP
  exact (padicPairLPolynomial_spec F T hnr ψ ν π σ hπ hσ μ hμ).unique hP

/-- The actual rational-function unit associated with the normalized pair polynomial. -/
def padicPairLFactor :
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
      (_ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (_hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
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
  intro ψ ν π σ hπ hσ
  exact pairLFactor
    (padicPairLPolynomialExists_canonical F T hnr ψ ν π σ hπ hσ)

/-- The selected unit is the reciprocal of the selected polynomial. -/
@[simp] theorem coe_padicPairLFactor :
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
      (ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      (padicPairLFactor F T hnr ψ ν π σ hπ hσ : RationalFunctions) =
        (algebraMap ℂ[X] RationalFunctions
          (padicPairLPolynomial F T hnr ψ ν π σ hπ hσ))⁻¹ := by
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
  intro ψ ν π σ hπ hσ
  rfl

/-- Reciprocal characterization by any polynomial certified for the pair. -/
theorem padicPairLFactor_eq :
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
      (ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier))
        (_hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ),
      ∀ {P : ℂ[X]},
        IsPairLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) μ ν π σ P →
        (padicPairLFactor F T hnr ψ ν π σ hπ hσ : RationalFunctions) =
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
  intro ψ ν π σ hπ hσ μ hμ P hP
  rw [coe_padicPairLFactor, padicPairLPolynomial_eq F T hnr ψ ν π σ hπ hσ μ hμ hP]

/-- Agreement with the existing supplied-topology canonical constructor. -/
theorem padicPairLFactor_eq_canonicalPairLFactor :
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
      (ν : AdditiveHaarMeasure F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
      (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
      ∀ (h : PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar F.Carrier n) ν π σ),
        padicPairLFactor F T hnr ψ ν π σ hπ hσ =
          canonicalPairLFactor T n r ψ ν π σ h := by
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
  intro ψ ν π σ hπ hσ h
  apply Units.ext
  rw [coe_padicPairLFactor,
    canonicalPairLFactor_eq T n r ψ ν π σ h _
      (padicPairLPolynomial_spec F T hnr ψ ν π σ hπ hσ _
        (unipotentQuotientHaar_isCompatible F.Carrier n))]

end SuppliedTopology

section Generic

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : MeasurableSpace F.Carrier := borel F.Carrier

variable {n r : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (hnr : n ≤ r)
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

/-- The normalized polynomial for a generic pair with canonical topology. -/
def genericPairLPolynomial : ℂ[X] :=
  padicPairLPolynomial F F.canonicalTopologicalData hnr ψ ν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The actual rational-function L-factor for a generic pair with canonical topology. -/
def genericPairLFactor : RationalFunctionsˣ :=
  padicPairLFactor F F.canonicalTopologicalData hnr ψ ν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

@[simp] theorem coe_genericPairLFactor :
    (genericPairLFactor F hnr ψ ν π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions
        (genericPairLPolynomial F hnr ψ ν π σ hπ hσ))⁻¹ := rfl

@[simp] theorem genericPairLPolynomial_coeff_zero :
    (genericPairLPolynomial F hnr ψ ν π σ hπ hσ).coeff 0 = 1 :=
  padicPairLPolynomial_coeff_zero F F.canonicalTopologicalData hnr ψ ν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The complete existing relation includes compatible-measure existence, so
the universal specification is not vacuous. -/
theorem genericPairLPolynomial_isPadic :
    IsPadicPairLPolynomial F ψ ν π σ
      (genericPairLPolynomial F hnr ψ ν π σ hπ hσ) := by
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
    exact padicPairLPolynomial_spec F F.canonicalTopologicalData hnr ψ ν π σ
      (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)
      μ hμ

theorem genericPairLPolynomial_eq {P : ℂ[X]}
    (hP : IsPadicPairLPolynomial F ψ ν π σ P) :
    genericPairLPolynomial F hnr ψ ν π σ hπ hσ = P :=
  (genericPairLPolynomial_isPadic F hnr ψ ν π σ hπ hσ).unique hP

theorem genericPairLFactor_eq {P : ℂ[X]}
    (hP : IsPadicPairLPolynomial F ψ ν π σ P) :
    (genericPairLFactor F hnr ψ ν π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  rw [coe_genericPairLFactor, genericPairLPolynomial_eq F hnr ψ ν π σ hπ hσ hP]

end Generic

end Langlands.RankinSelberg
