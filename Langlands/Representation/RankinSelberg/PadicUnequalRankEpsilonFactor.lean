import Langlands.Representation.RankinSelberg.UnequalRankFunctionalEquationProof
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.PairEpsilonFactor
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! Constructed unequal-rank p-adic epsilon data, rational units and spectral values. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

private theorem valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section SuppliedTopology

variable (T : F.TopologicalData) {n r : ℕ}
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (hnr : n < r)

include hnr

/-- Actual epsilon existence from the published full unequal-rank equation. -/
theorem padicUnequalRankEpsilonFactorExists :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (_hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (_hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    PairEpsilonFactorExists T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ
  obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
  obtain ⟨ℓ', hℓ'⟩ := hσ.exists_ne_zero
  have hFE := unequalRankFunctionalEquation.{uF,uV,uW} F T n r hnr ψ
    (unipotentQuotientHaar F.Carrier n)
    (unipotentQuotientHaar_isCompatible F.Carrier n) ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨c, m, hEq⟩ := exists_unequalRankEpsilonEquation_iff.mpr hFE
  exact ⟨(c, m), (isPairEpsilonFactor_of_lt hnr).mpr
    (unequalRankEpsilonFactor_of_equation hnr hπ hσ hℓ hℓ' hEq)⟩

/-- The actual coefficient and integer exponent of the unequal-rank epsilon factor. -/
def padicUnequalRankEpsilonData :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (_hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (_hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ℂˣ × ℤ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ
  exact pairEpsilonData (padicUnequalRankEpsilonFactorExists F T hnr ψ ν hν π σ hπ hσ)

/-- The selected monomial satisfies the full all-measure, all-functional pair relation. -/
theorem padicUnequalRankEpsilonData_spec :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    IsPairEpsilonFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ (padicUnequalRankEpsilonData F T hnr ψ ν hν π σ hπ hσ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ
  exact pairEpsilonData_spec (padicUnequalRankEpsilonFactorExists F T hnr ψ ν hν π σ hπ hσ)

/-- The selected epsilon data agree with every other witness of the same relation. -/
theorem padicUnequalRankEpsilonData_eq :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ∀ {e : ℂˣ × ℤ}, IsPairEpsilonFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ e →
      padicUnequalRankEpsilonData F T hnr ψ ν hν π σ hπ hσ = e := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ e he
  exact pairEpsilonData_eq T.residueCardinality_gt_one (padicUnequalRankEpsilonFactorExists F T hnr ψ ν hν π σ hπ hσ) he

/-- The actual nonzero rational monomial in X = q^(-s), with supplied self-dual measure. -/
def padicUnequalRankEpsilonFactor :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (_hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (_hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    RationalFunctionsˣ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ
  exact pairEpsilonFactor hν (padicUnequalRankEpsilonFactorExists F T hnr ψ ν hν π σ hπ hσ)

/-- The exact rational-function formula for the constructed epsilon factor. -/
@[simp] theorem coe_padicUnequalRankEpsilonFactor :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    (padicUnequalRankEpsilonFactor F T hnr ψ ν hν π σ hπ hσ : RationalFunctions) =
      algebraMap ℂ RationalFunctions ((padicUnequalRankEpsilonData F T hnr ψ ν hν π σ hπ hσ).1 : ℂ) *
        RatFunc.X ^ (padicUnequalRankEpsilonData F T hnr ψ ν hν π σ hπ hσ).2 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ
  exact coe_pairEpsilonFactor hν (padicUnequalRankEpsilonFactorExists F T hnr ψ ν hν π σ hπ hσ)

/-- Characterization of the constructed rational unit by any certified epsilon data. -/
theorem padicUnequalRankEpsilonFactor_eq :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ∀ {e : ℂˣ × ℤ}, IsPairEpsilonFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ e →
      padicUnequalRankEpsilonFactor F T hnr ψ ν hν π σ hπ hσ = rationalEpsilonMonomial e.1 e.2 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ e he
  exact pairEpsilonFactor_eq T.residueCardinality_gt_one hν (padicUnequalRankEpsilonFactorExists F T hnr ψ ν hν π σ hπ hσ) he

/-- The everywhere nonzero spectral epsilon value, as a complex unit. -/
def padicUnequalRankEpsilonValue :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (_hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (_hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (_hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ℂ → ℂˣ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ
  exact pairEpsilonValue T.residueCardinality_gt_one hν (padicUnequalRankEpsilonFactorExists F T hnr ψ ν hν π σ hπ hσ)

/-- The exact complex-monomial formula at every spectral parameter. -/
@[simp] theorem coe_padicUnequalRankEpsilonValue :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ∀ s : ℂ, (padicUnequalRankEpsilonValue F T hnr ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial T.residueCardinality (padicUnequalRankEpsilonData F T hnr ψ ν hν π σ hπ hσ).1
        (padicUnequalRankEpsilonData F T hnr ψ ν hν π σ hπ hσ).2 s := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ s
  rfl

/-- The spectral value equals the monomial of any certified coefficient and exponent. -/
theorem padicUnequalRankEpsilonValue_eq :
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ∀ {e : ℂˣ × ℤ}, IsPairEpsilonFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ e →
      ∀ s : ℂ, (padicUnequalRankEpsilonValue F T hnr ψ ν hν π σ hπ hσ s : ℂ) = epsilonMonomial T.residueCardinality e.1 e.2 s := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ ν hν π σ hπ hσ e he s
  rw [coe_padicUnequalRankEpsilonValue, padicUnequalRankEpsilonData_eq F T hnr ψ ν hν π σ hπ hσ he]

end SuppliedTopology

section Generic

local instance padicUnequalRankEpsilonNormedField : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance padicUnequalRankEpsilonValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance padicUnequalRankEpsilonLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance padicUnequalRankEpsilonNonarchimedeanAddGroup : NonarchimedeanAddGroup F.Carrier := valuative_nonarchimedean
local instance padicUnequalRankEpsilonMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance padicUnequalRankEpsilonBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

variable {n r : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (hnr : n < r) (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

/-- The actual unequal-rank epsilon coefficient and integer exponent for a generic pair. -/
def genericUnequalRankEpsilonData : ℂˣ × ℤ :=
  padicUnequalRankEpsilonData F F.canonicalTopologicalData hnr ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The actual unequal-rank epsilon rational-function unit for a generic pair. -/
def genericUnequalRankEpsilonFactor : RationalFunctionsˣ :=
  padicUnequalRankEpsilonFactor F F.canonicalTopologicalData hnr ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The actual unequal-rank epsilon everywhere nonzero spectral value for a generic pair. -/
def genericUnequalRankEpsilonValue : ℂ → ℂˣ :=
  padicUnequalRankEpsilonValue F F.canonicalTopologicalData hnr ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The generic constructor satisfies the existing intrinsic p-adic relation. -/
theorem genericUnequalRankEpsilonData_isPadic :
    IsPadicPairEpsilonFactor F ψ ν π σ
      (genericUnequalRankEpsilonData F hnr ψ ν hν π σ hπ hσ) :=
  padicUnequalRankEpsilonData_spec F F.canonicalTopologicalData hnr ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

theorem genericUnequalRankEpsilonData_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    genericUnequalRankEpsilonData F hnr ψ ν hν π σ hπ hσ = e :=
  (genericUnequalRankEpsilonData_isPadic F hnr ψ ν hν π σ hπ hσ).unique he

@[simp] theorem coe_genericUnequalRankEpsilonFactor :
    (genericUnequalRankEpsilonFactor F hnr ψ ν hν π σ hπ hσ : RationalFunctions) =
      algebraMap ℂ RationalFunctions
        ((genericUnequalRankEpsilonData F hnr ψ ν hν π σ hπ hσ).1 : ℂ) *
        RatFunc.X ^ (genericUnequalRankEpsilonData F hnr ψ ν hν π σ hπ hσ).2 :=
  coe_padicUnequalRankEpsilonFactor F F.canonicalTopologicalData hnr ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

theorem genericUnequalRankEpsilonFactor_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    genericUnequalRankEpsilonFactor F hnr ψ ν hν π σ hπ hσ = rationalEpsilonMonomial e.1 e.2 := by
  apply Units.ext
  rw [coe_genericUnequalRankEpsilonFactor,
    genericUnequalRankEpsilonData_eq F hnr ψ ν hν π σ hπ hσ he, coe_rationalEpsilonMonomial]

@[simp] theorem coe_genericUnequalRankEpsilonValue (s : ℂ) :
    (genericUnequalRankEpsilonValue F hnr ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality
        (genericUnequalRankEpsilonData F hnr ψ ν hν π σ hπ hσ).1
        (genericUnequalRankEpsilonData F hnr ψ ν hν π σ hπ hσ).2 s := rfl

theorem genericUnequalRankEpsilonValue_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) (s : ℂ) :
    (genericUnequalRankEpsilonValue F hnr ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality e.1 e.2 s := by
  rw [coe_genericUnequalRankEpsilonValue, genericUnequalRankEpsilonData_eq F hnr ψ ν hν π σ hπ hσ he]

end Generic

end Langlands.RankinSelberg
