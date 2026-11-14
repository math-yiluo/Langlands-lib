import Langlands.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.AllField.Representation.RankinSelberg.PadicGammaFactor
/-! Gamma construction with dual Whittaker type derived from the original pair. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section DualType


end DualType

section Assembly


end Assembly

private theorem gammaInputTotallyDisconnected (F : Type uF) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsValuativeTopology F] [T2Space F] :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (ψ : UnitaryAdditiveCharacter F)
  (ν : letI := borel F
    AdditiveHaarMeasure F)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

/-- Sufficient canonical p-adic inputs retaining original type, both analytic
conclusions, self-duality and epsilon existence. Dual type is derived. -/
def PadicPairGammaConstructionInput : Prop :=
  letI := (⟨⟩ : LocalFieldData F).fieldT2
  letI := gammaInputTotallyDisconnected F
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let q := (⟨⟩ : LocalFieldData F).residueCardinality
  let abv := normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
  let μ := unipotentQuotientHaar F n
  n ≤ r ∧ IsSelfDual ψ ν ∧ PairEpsilonFactorExists q ψ abv ν π σ ∧
    IsOfWhittakerType r (standardCharacter ψ r) π ∧
    IsOfWhittakerType n (inverseStandardCharacter ψ n) σ ∧
    PairAnalyticInput q ψ abv μ ν π σ ∧
    PairAnalyticInput q (ψ.scale (-1)) abv μ ν
      (inverseTransposePullback π) (inverseTransposePullback σ)

/-- The reduced inputs are equivalent to the published input predicate; the
omitted dual type conditions follow from the original ones. -/
theorem padicPairGammaConstructionInput_iff :
    PadicPairGammaConstructionInput F ψ ν π σ ↔ PadicPairGammaInput F ψ ν π σ := by
  let := (⟨⟩ : LocalFieldData F).fieldT2
  let := gammaInputTotallyDisconnected F
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  constructor
  · rintro ⟨hnr, hν, hε, hπ, hσ, hA, hAd⟩
    exact ⟨hnr, hν, hε, hπ, hσ, isOfWhittakerType_firstDual ψ π hπ,
      isOfWhittakerType_secondDual ψ σ hσ, hA, hAd⟩
  · rintro ⟨hnr, hν, hε, hπ, hσ, _, _, hA, hAd⟩
    exact ⟨hnr, hν, hε, hπ, hσ, hA, hAd⟩

/-- The canonical p-adic gamma unit, with both dual Whittaker-type obligations
discharged by transport. -/
def padicPairGammaFactorOfWhittakerType
    (h : PadicPairGammaConstructionInput F ψ ν π σ) :
    {G : RationalFunctionsˣ // IsPadicPairGammaFactor F ψ ν π σ (G : RationalFunctions)} :=
  padicPairGammaFactor F ψ ν π σ ((padicPairGammaConstructionInput_iff F ψ ν π σ).mp h)

/-- Reduced construction inputs using the existing larger-rank-first convention. -/
def PadicSymmetricGammaConstructionInput : Prop :=
  if n ≤ r then PadicPairGammaConstructionInput F ψ ν π σ
  else PadicPairGammaConstructionInput F ψ ν σ π

/-- The larger-rank-first input reduction works for both rank orders. -/
theorem padicSymmetricGammaConstructionInput_iff :
    PadicSymmetricGammaConstructionInput F ψ ν π σ ↔
      PadicSymmetricGammaInput F ψ ν π σ := by
  by_cases hnr : n ≤ r
  · simpa only [PadicSymmetricGammaConstructionInput, PadicSymmetricGammaInput,
      ite_eq_left hnr] using padicPairGammaConstructionInput_iff F ψ ν π σ
  · simpa only [PadicSymmetricGammaConstructionInput, PadicSymmetricGammaInput,
      ite_eq_right hnr] using padicPairGammaConstructionInput_iff F ψ ν σ π

/-- A certified gamma unit in either rank order with derived dual type. -/
def padicSymmetricGammaFactorOfWhittakerType
    (h : PadicSymmetricGammaConstructionInput F ψ ν π σ) :
    {G : RationalFunctionsˣ // IsPadicSymmetricGammaFactor F ψ ν π σ
      (G : RationalFunctions)} :=
  padicSymmetricGammaFactor F ψ ν π σ
    ((padicSymmetricGammaConstructionInput_iff F ψ ν π σ).mp h)

end Padic

end Langlands.AllField.RankinSelberg
