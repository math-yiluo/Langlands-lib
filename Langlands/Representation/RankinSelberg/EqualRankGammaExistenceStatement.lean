import Langlands.Representation.RankinSelberg.GammaFactor

/-! Equal-rank gamma existence, isolated from JPSS Theorem 2.7(iii). -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The valuation topology has a basis of open additive subgroups. This
bridges existing Mathlib classes without adding a hypothesis to the targets. -/
theorem equalRankGamma_valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Derived gamma-existence target for equal positive ranks, with precisely the
scope of `EqualRankFunctionalEquationStatement` and the existing gamma predicate. -/
def EqualRankGammaExistenceStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := equalRankGamma_valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier, IsSelfDual ψ ν →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∃ G : RationalFunctions,
            EqualRankGammaEquation T.residueCardinality ψ
              (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' G

end Langlands.RankinSelberg
