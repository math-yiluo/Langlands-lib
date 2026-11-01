import Langlands.Representation.RankinSelberg.EqualRankFunctionalEquationProof
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.PairEpsilonFactor
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! Constructed equal-rank p-adic epsilon data, rational units and spectral values. -/

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

variable (T : F.TopologicalData) {n : ℕ}
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Actual epsilon existence from the published full equal-rank equation. -/
theorem padicEqualRankEpsilonFactorExists :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (_hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
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
  have hFE := equalRankFunctionalEquation.{uF,uV,uW} F T n ψ
    (unipotentQuotientHaar F.Carrier n)
    (unipotentQuotientHaar_isCompatible F.Carrier n) ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨c, m, hEq⟩ := exists_equalRankEpsilonEquation_iff.mpr hFE
  exact ⟨(c, m), isPairEpsilonFactor_self.mpr
    (equalRankEpsilonFactor_of_equation hπ hσ hℓ hℓ' hEq)⟩

/-- The actual coefficient and integer exponent of the equal-rank epsilon factor. -/
def padicEqualRankEpsilonData :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (_hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
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
  exact pairEpsilonData (padicEqualRankEpsilonFactorExists F T ψ ν hν π σ hπ hσ)

/-- The selected monomial satisfies the full all-measure, all-functional pair relation. -/
theorem padicEqualRankEpsilonData_spec :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    IsPairEpsilonFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ (padicEqualRankEpsilonData F T ψ ν hν π σ hπ hσ) := by
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
  exact pairEpsilonData_spec (padicEqualRankEpsilonFactorExists F T ψ ν hν π σ hπ hσ)

/-- The selected epsilon data agree with every other witness of the same relation. -/
theorem padicEqualRankEpsilonData_eq :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ∀ {e : ℂˣ × ℤ}, IsPairEpsilonFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ e →
      padicEqualRankEpsilonData F T ψ ν hν π σ hπ hσ = e := by
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
  exact pairEpsilonData_eq T.residueCardinality_gt_one (padicEqualRankEpsilonFactorExists F T ψ ν hν π σ hπ hσ) he

/-- The actual nonzero rational monomial in X = q^(-s), with supplied self-dual measure. -/
def padicEqualRankEpsilonFactor :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (_hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
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
  exact pairEpsilonFactor hν (padicEqualRankEpsilonFactorExists F T ψ ν hν π σ hπ hσ)

/-- The exact rational-function formula for the constructed epsilon factor. -/
@[simp] theorem coe_padicEqualRankEpsilonFactor :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    (padicEqualRankEpsilonFactor F T ψ ν hν π σ hπ hσ : RationalFunctions) =
      algebraMap ℂ RationalFunctions ((padicEqualRankEpsilonData F T ψ ν hν π σ hπ hσ).1 : ℂ) *
        RatFunc.X ^ (padicEqualRankEpsilonData F T ψ ν hν π σ hπ hσ).2 := by
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
  exact coe_pairEpsilonFactor hν (padicEqualRankEpsilonFactorExists F T ψ ν hν π σ hπ hσ)

/-- Characterization of the constructed rational unit by any certified epsilon data. -/
theorem padicEqualRankEpsilonFactor_eq :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ∀ {e : ℂˣ × ℤ}, IsPairEpsilonFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ e →
      padicEqualRankEpsilonFactor F T ψ ν hν π σ hπ hσ = rationalEpsilonMonomial e.1 e.2 := by
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
  exact pairEpsilonFactor_eq T.residueCardinality_gt_one hν (padicEqualRankEpsilonFactorExists F T ψ ν hν π σ hπ hσ) he

/-- The everywhere nonzero spectral epsilon value, as a complex unit. -/
def padicEqualRankEpsilonValue :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (_hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
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
  exact pairEpsilonValue T.residueCardinality_gt_one hν (padicEqualRankEpsilonFactorExists F T ψ ν hν π σ hπ hσ)

/-- The exact complex-monomial formula at every spectral parameter. -/
@[simp] theorem coe_padicEqualRankEpsilonValue :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ∀ s : ℂ, (padicEqualRankEpsilonValue F T ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial T.residueCardinality (padicEqualRankEpsilonData F T ψ ν hν π σ hπ hσ).1
        (padicEqualRankEpsilonData F T ψ ν hν π σ hπ hσ).2 s := by
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
theorem padicEqualRankEpsilonValue_eq :
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
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ),
    ∀ {e : ℂˣ × ℤ}, IsPairEpsilonFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν π σ e →
      ∀ s : ℂ, (padicEqualRankEpsilonValue F T ψ ν hν π σ hπ hσ s : ℂ) = epsilonMonomial T.residueCardinality e.1 e.2 s := by
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
  rw [coe_padicEqualRankEpsilonValue, padicEqualRankEpsilonData_eq F T ψ ν hν π σ hπ hσ he]

end SuppliedTopology

section Generic

local instance padicEqualRankEpsilonNormedField : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance padicEqualRankEpsilonValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance padicEqualRankEpsilonLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance padicEqualRankEpsilonNonarchimedeanAddGroup : NonarchimedeanAddGroup F.Carrier := valuative_nonarchimedean
local instance padicEqualRankEpsilonMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance padicEqualRankEpsilonBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ n π) (hσ : Whittaker.IsGeneric ψ n σ)

/-- The actual equal-rank epsilon coefficient and integer exponent for a generic pair. -/
def genericEqualRankEpsilonData : ℂˣ × ℤ :=
  padicEqualRankEpsilonData F F.canonicalTopologicalData ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The actual equal-rank epsilon rational-function unit for a generic pair. -/
def genericEqualRankEpsilonFactor : RationalFunctionsˣ :=
  padicEqualRankEpsilonFactor F F.canonicalTopologicalData ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The actual equal-rank epsilon everywhere nonzero spectral value for a generic pair. -/
def genericEqualRankEpsilonValue : ℂ → ℂˣ :=
  padicEqualRankEpsilonValue F F.canonicalTopologicalData ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The generic constructor satisfies the existing intrinsic p-adic relation. -/
theorem genericEqualRankEpsilonData_isPadic :
    IsPadicPairEpsilonFactor F ψ ν π σ
      (genericEqualRankEpsilonData F ψ ν hν π σ hπ hσ) :=
  padicEqualRankEpsilonData_spec F F.canonicalTopologicalData ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

theorem genericEqualRankEpsilonData_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    genericEqualRankEpsilonData F ψ ν hν π σ hπ hσ = e :=
  (genericEqualRankEpsilonData_isPadic F ψ ν hν π σ hπ hσ).unique he

@[simp] theorem coe_genericEqualRankEpsilonFactor :
    (genericEqualRankEpsilonFactor F ψ ν hν π σ hπ hσ : RationalFunctions) =
      algebraMap ℂ RationalFunctions
        ((genericEqualRankEpsilonData F ψ ν hν π σ hπ hσ).1 : ℂ) *
        RatFunc.X ^ (genericEqualRankEpsilonData F ψ ν hν π σ hπ hσ).2 :=
  coe_padicEqualRankEpsilonFactor F F.canonicalTopologicalData ψ ν hν π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfInverseWhittakerType_of_isGeneric F hσ)

theorem genericEqualRankEpsilonFactor_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    genericEqualRankEpsilonFactor F ψ ν hν π σ hπ hσ = rationalEpsilonMonomial e.1 e.2 := by
  apply Units.ext
  rw [coe_genericEqualRankEpsilonFactor,
    genericEqualRankEpsilonData_eq F ψ ν hν π σ hπ hσ he, coe_rationalEpsilonMonomial]

@[simp] theorem coe_genericEqualRankEpsilonValue (s : ℂ) :
    (genericEqualRankEpsilonValue F ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality
        (genericEqualRankEpsilonData F ψ ν hν π σ hπ hσ).1
        (genericEqualRankEpsilonData F ψ ν hν π σ hπ hσ).2 s := rfl

theorem genericEqualRankEpsilonValue_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) (s : ℂ) :
    (genericEqualRankEpsilonValue F ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality e.1 e.2 s := by
  rw [coe_genericEqualRankEpsilonValue, genericEqualRankEpsilonData_eq F ψ ν hν π σ hπ hσ he]

end Generic

end Langlands.RankinSelberg
