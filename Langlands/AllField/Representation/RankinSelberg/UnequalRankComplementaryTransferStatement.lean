import Langlands.Representation.RankinSelberg.UnequalRankComplementaryTransferStatement
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement
/-! Paired complementary-block transfer target derived from JPSS §2.8. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankComplementaryTransferStatement UnequalRankFunctionalEquationStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- The valuation topology has a basis of open additive subgroups. This
bridges existing Mathlib classes without adding a hypothesis to the targets. -/
private theorem complementaryTransfer_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- For every adjacent pair of blocks, one coefficient in the original model
transfers both actual integral functions on respective right half-planes.
This derived interface asserts no functional equation or continuation. -/
def UnequalRankComplementaryTransferStatement (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI := complementaryTransfer_nonarchimedean (K := F)
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
          ∀ (j k : ℕ) (hr : r = n + (j + k + 2)),
          ∀ f : (coefficientModel π ℓ).toSubmodule,
          ∀ f' : (coefficientModel σ ℓ').toSubmodule,
            ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
            ∃ a b : ℝ,
              (∀ s : ℂ, a < s.re →
                unequalRankIntegralAt (j + 1) k (by omega) ψ
                    (normalizedAbsoluteValue T) μ
                    (rectangularMeasure ν (j + 1) (n + 1)) f.val f'.val s =
                  unequalRankIntegralAt j (k + 1) (by omega) ψ
                    (normalizedAbsoluteValue T) μ
                    (rectangularMeasure ν j (n + 1)) f₀.val f'.val s) ∧
              (∀ s : ℂ, b < s.re →
                dualUnequalRankModelIntegralAt hnr (j + 1) k (by omega) ψ
                    (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' f f' s =
                  dualUnequalRankModelIntegralAt hnr j (k + 1) (by omega) ψ
                    (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' f₀ f' s)

end Langlands.AllField.RankinSelberg
