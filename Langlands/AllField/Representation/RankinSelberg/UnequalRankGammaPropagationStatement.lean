import Langlands.Representation.RankinSelberg.UnequalRankGammaPropagationStatement
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement
/-! Same-multiplier propagation from block zero, as a derived JPSS §2.8 target. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankFunctionalEquationStatement UnequalRankGammaPropagationStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- The valuation topology has a basis of open additive subgroups. This
bridges existing Mathlib classes without adding a hypothesis to the targets. -/
private theorem propagation_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- The actual block-zero gamma equation for a given rational function `G`
propagates to every complementary block with that same `G`. This proposition
is the derived prerequisite corresponding to JPSS §2.8; it is not proved here. -/
def UnequalRankGammaPropagationStatement (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI := propagation_nonarchimedean (K := F)
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  ∀ hnr : n < r,
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ ν : AdditiveHaarMeasure F, IsSelfDual ψ ν →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ G : RationalFunctions,
            (∃ ζ : ℂˣ, HasModelMinusOneScalar σ ℓ' ζ ∧
              (∃ R ∈ unequalRankValuesAt 0 (r - n - 1) (by omega)
                  T.residueCardinality ψ (normalizedAbsoluteValue T) μ
                  (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ', R ≠ 0) ∧
              ∀ f : (coefficientModel π ℓ).toSubmodule,
              ∀ f' : (coefficientModel σ ℓ').toSubmodule,
                ∃ R Rdual : RationalFunctions,
                  HasRationalContinuation T.residueCardinality
                    (unequalRankIntegralAt 0 (r - n - 1) (by omega) ψ
                      (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1))
                      f.val f'.val) R ∧
                  HasRationalContinuation T.residueCardinality
                    (dualUnequalRankModelIntegralAt hnr 0 (r - n - 1) (by omega) ψ
                      (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' f f') Rdual ∧
                  GammaFunctionalEquation T.residueCardinality ζ r G R Rdual) →
            UnequalRankGammaEquation hnr T.residueCardinality ψ
              (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' G

end Langlands.AllField.RankinSelberg
