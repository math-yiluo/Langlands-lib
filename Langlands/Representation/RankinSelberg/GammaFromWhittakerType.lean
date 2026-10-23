import Langlands.Representation.RankinSelberg.PadicGammaFactor
import Langlands.Representation.RankinSelberg.DualWhittakerType

/-! Gamma construction with dual Whittaker type derived from the original pair. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration

universe uF uV uW

section DualType

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The first representation in the dual pair has standard type for the inverse
additive character, derived from its original standard type. -/
theorem isOfWhittakerType_firstDual
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    IsOfWhittakerType n (standardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback π) := by
  simpa only [standardCharacter_scale_neg_one] using
    isOfWhittakerType_inverseTransposePullback ψ π hπ

/-- The second representation has inverse-standard type for the inverse additive
character, derived from its original inverse-standard type. -/
theorem isOfWhittakerType_secondDual
    (hπ : IsOfWhittakerType n (inverseStandardCharacter ψ n) π) :
    IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback π) := by
  simpa only [inverseStandardCharacter_scale_neg_one] using
    isOfWhittakerType_inverseTransposePullback_inverse ψ π hπ

end DualType

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

/-- Construct the certified gamma unit from the original Whittaker-type pair.
The two analytic inputs and epsilon existence remain explicit. -/
def gammaFactorOfWhittakerType (hnr : n ≤ r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hA : PairAnalyticInput q ψ abv μ ν π σ)
    (hAd : PairAnalyticInput q (ψ.scale (-1)) abv μ ν
      (inverseTransposePullback π) (inverseTransposePullback σ))
    (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ) :
    {G : RationalFunctionsˣ // IsPairGammaFactor q ψ abv ν π σ (G : RationalFunctions)} :=
  gammaFactorOfAnalyticInput hnr hπ hσ
    (isOfWhittakerType_firstDual ψ π hπ) (isOfWhittakerType_secondDual ψ σ hσ)
    hA hAd hq hν hμ hε

end Assembly

private theorem gammaInputTotallyDisconnected (F : Type uF) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsValuativeTopology F] [T2Space F] :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)

/-- Sufficient canonical p-adic inputs retaining original type, both analytic
conclusions, self-duality and epsilon existence. Dual type is derived. -/
def PadicPairGammaConstructionInput : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := F.canonicalTopologicalData.fieldT2
  letI := gammaInputTotallyDisconnected F.Carrier
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
    PairAnalyticInput q ψ abv μ ν π σ ∧
    PairAnalyticInput q (ψ.scale (-1)) abv μ ν
      (inverseTransposePullback π) (inverseTransposePullback σ)

/-- The reduced inputs are equivalent to the published input predicate; the
omitted dual type conditions follow from the original ones. -/
theorem padicPairGammaConstructionInput_iff :
    PadicPairGammaConstructionInput F ψ ν π σ ↔ PadicPairGammaInput F ψ ν π σ := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  let := gammaInputTotallyDisconnected F.Carrier
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
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

end Langlands.RankinSelberg
