import Langlands.Representation.RankinSelberg.EqualRankGammaFactor
import Langlands.Representation.RankinSelberg.UnequalRankGammaFactor
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.LocalField.Topology
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration

universe uF uV uW

private theorem valuativeTotallyDisconnected (F : Type uF) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsValuativeTopology F] [T2Space F] :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

section Analytic

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {r n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The published analytic conclusion for every nonzero functional pair: the
Schwartz-test family in equal rank, and every rectangular block in unequal rank.
This is an input proposition, not an assertion that the analytic results hold. -/
def PairAnalyticInput (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) : Prop :=
  if hr : r = n then by
    subst r
    exact ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 → EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ'
  else
    ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 → ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
        UnequalRankAnalyticAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ'

end Analytic

section Assembly

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
  [T2Space F] [TotallyDisconnectedSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- Assemble the accepted equal- and unequal-rank constructions. The dual
analytic input concerns the actual inverse-transpose representation. -/
def gammaFactorOfAnalyticInput (hnr : n ≤ r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hπd : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
      (inverseTransposePullback π))
    (hσd : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ))
    (hA : PairAnalyticInput q ψ abv μ ν π σ)
    (hAd : PairAnalyticInput q (ψ.scale (-1)) abv μ ν
      (inverseTransposePullback π) (inverseTransposePullback σ))
    (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ) :
    {G : RationalFunctionsˣ // IsPairGammaFactor q ψ abv ν π σ (G : RationalFunctions)} := by
  by_cases hr : r = n
  · subst r
    simp only [PairAnalyticInput] at hA hAd
    exact equalRankGammaFactor hπ hσ hπd hσd hA
      (fun ℓ ℓ' hℓ hℓ' => hAd _ _ (firstDualFunctional_ne_zero ψ π hℓ)
        (secondDualFunctional_ne_zero ψ σ hℓ')) hq hν hμ hε
  · simp only [PairAnalyticInput, dite_eq_right hr] at hA hAd
    exact unequalRankGammaFactor (by omega) hπ hσ hπd hσd hA
      (fun ℓ ℓ' hℓ hℓ' => hAd _ _ (firstDualFunctional_ne_zero ψ π hℓ)
        (secondDualFunctional_ne_zero ψ σ hℓ')) hq hν hμ hε

end Assembly

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)

/-- Explicit sufficient inputs for canonical p-adic gamma construction. The
quotient measure is constructed; analytic conclusions and epsilon existence
remain assumptions. All four Whittaker-type hypotheses are retained. -/
def PadicPairGammaInput : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := F.canonicalTopologicalData.fieldT2
  letI := valuativeTotallyDisconnected F.Carrier
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let q := F.canonicalTopologicalData.residueCardinality
  let abv := normalizedAbsoluteValue F.canonicalTopologicalData
  let μ := unipotentQuotientHaar F.Carrier n
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
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := F.canonicalTopologicalData.fieldT2
  letI := valuativeTotallyDisconnected F.Carrier
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  obtain ⟨hnr, hν, hε, hπ, hσ, hπd, hσd, hA, hAd⟩ := h
  exact gammaFactorOfAnalyticInput hnr hπ hσ hπd hσd hA hAd
    (PadicField.TopologicalData.residueCardinality_gt_one _)
    hν (unipotentQuotientHaar_isCompatible F.Carrier n) hε

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

end Langlands.RankinSelberg
