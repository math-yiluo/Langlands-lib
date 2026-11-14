import Langlands.Representation.RankinSelberg.PadicGammaFactor
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial PadicPairGammaInput PadicSymmetricGammaInput QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply padicPairGammaFactor padicSymmetricGammaFactor
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

private theorem valuativeTotallyDisconnected (F : Type uF) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsValuativeTopology F] [T2Space F] :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

section Analytic


end Analytic

section Assembly


end Assembly

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (ψ : UnitaryAdditiveCharacter F)
  (ν : letI := borel F
    AdditiveHaarMeasure F)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

/-- Explicit sufficient inputs for canonical p-adic gamma construction. The
quotient measure is constructed; analytic conclusions and epsilon existence
remain assumptions. All four Whittaker-type hypotheses are retained. -/
def PadicPairGammaInput : Prop :=
  letI := (⟨⟩ : LocalFieldData F).fieldT2
  letI := valuativeTotallyDisconnected F
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
    IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) (inverseTransposePullback π) ∧
    IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n) (inverseTransposePullback σ) ∧
    PairAnalyticInput q ψ abv μ ν π σ ∧
    PairAnalyticInput q (ψ.scale (-1)) abv μ ν
      (inverseTransposePullback π) (inverseTransposePullback σ)

/-- A canonical p-adic gamma unit with the existing universal specification.
No quotient-measure or L-polynomial existence input is required. -/
def padicPairGammaFactor (h : PadicPairGammaInput F ψ ν π σ) :
    {G : RationalFunctionsˣ // IsPadicPairGammaFactor F ψ ν π σ (G : RationalFunctions)} := by
  letI := (⟨⟩ : LocalFieldData F).fieldT2
  letI := valuativeTotallyDisconnected F
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  obtain ⟨hnr, hν, hε, hπ, hσ, hπd, hσd, hA, hAd⟩ := h
  exact gammaFactorOfAnalyticInput hnr hπ hσ hπd hσd hA hAd
    (Langlands.LocalFieldData.residueCardinality_gt_one _)
    hν (unipotentQuotientHaar_isCompatible F n) hε

/-- Sufficient construction inputs for either rank order, following the existing
larger-rank-first convention of `IsPadicSymmetricGammaFactor`. -/
def PadicSymmetricGammaInput : Prop :=
  if n ≤ r then PadicPairGammaInput F ψ ν π σ else PadicPairGammaInput F ψ ν σ π

/-- The gamma unit for either rank order with the published symmetric relation.
The rank-order branch is a convention; no rank-exchange theorem is asserted. -/
def padicSymmetricGammaFactor (h : PadicSymmetricGammaInput F ψ ν π σ) :
    {G : RationalFunctionsˣ // IsPadicSymmetricGammaFactor F ψ ν π σ (G : RationalFunctions)} := by
  by_cases hnr : n ≤ r
  · have hi : PadicPairGammaInput F ψ ν π σ := by
      simpa only [PadicSymmetricGammaInput, ite_eq_left hnr] using h
    exact ⟨(padicPairGammaFactor F ψ ν π σ hi).val,
      (isPadicSymmetricGammaFactor_of_le hnr).mpr (padicPairGammaFactor F ψ ν π σ hi).property⟩
  · have hi : PadicPairGammaInput F ψ ν σ π := by
      simpa only [PadicSymmetricGammaInput, ite_eq_right hnr] using h
    exact ⟨(padicPairGammaFactor F ψ ν σ π hi).val,
      (isPadicSymmetricGammaFactor_of_lt (Nat.lt_of_not_ge hnr)).mpr
        (padicPairGammaFactor F ψ ν σ π hi).property⟩

end Padic

end Langlands.AllField.RankinSelberg
