import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.Representation.RankinSelberg.UnipotentQuotient

/-!
# Character transport and fixed-monomial epsilon adapters

These closed proposition definitions package internal consequences of the
published Whittaker functional-space and quotient-measure interfaces.
They do not prove an analytic or functional-equation theorem.
-/

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

/-- Standard and inverse-standard full Whittaker type for the same actual
representation are equivalent. Admissibility and finite generation are retained. -/
def WhittakerTypeCharacterTransportStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
    IsOfWhittakerType n (standardCharacter ψ n) π ↔
      IsOfWhittakerType n (inverseStandardCharacter ψ n) π

/-- A fixed epsilon monomial valid at the canonical quotient measure for one
specified nonzero functional pair is an equal-rank epsilon factor for the same
monomial. Full Whittaker type supplies the functional-space multiplicity one. -/
def EqualRankEpsilonUniformityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)]
    [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [BorelSpace (LeftUnipotentQuotient n F)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    IsOfWhittakerType n (standardCharacter ψ n) π →
    IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      ∀ (c : ℂˣ) (m : ℤ),
        EqualRankEpsilonEquation q ψ abv (unipotentQuotientHaar F n) ν π σ ℓ ℓ' c m →
        IsEqualRankEpsilonFactor q ψ abv ν π σ (c, m)

/-- The corresponding fixed-monomial adapter for ranks `r + 1 > n + 1`.
The existing equation retains its quantification over every rectangular block. -/
def UnequalRankEpsilonUniformityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (n r : ℕ) (hnr : n < r)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)]
    [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [BorelSpace (LeftUnipotentQuotient n F)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    IsOfWhittakerType r (standardCharacter ψ r) π →
    IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
    ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      ∀ (c : ℂˣ) (m : ℤ),
        UnequalRankEpsilonEquation hnr q ψ abv (unipotentQuotientHaar F n) ν
          π σ ℓ ℓ' c m →
        IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ (c, m)

/-- Same-representation character transport and both fixed-monomial epsilon
uniformity adapters, with independent field and representation universes. -/
def WhittakerGammaAdaptersStatement : Prop :=
  WhittakerTypeCharacterTransportStatement.{uF, uV} ∧
  EqualRankEpsilonUniformityStatement.{uF, uV, uW} ∧
  UnequalRankEpsilonUniformityStatement.{uF, uV, uW}

end Langlands.RankinSelberg
