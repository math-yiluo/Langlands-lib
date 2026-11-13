import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-!
# Continued unequal-rank bilinear forms at block zero

This conditional interface isolates the construction of the actual continued
integrals with the covariance of JPSS (2.11.2) and (2.11.4). It states neither
analytic continuation existence nor bilinear uniqueness nor gamma existence.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankBlockZeroContinuedFormsStatement UnequalRankCommonGeneratorStatement UnequalRankFunctionalEquationStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section FixedData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end FixedData

/-- The valuative topology supplies the additive nonarchimedean structure
used in the parent block-zero functional-equation scope. -/
private theorem continuedForms_valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

/-- Conditional construction of the two block-zero continued bilinear forms.
The only analytic premises are the original `(0,k)` and inverse-transpose
`(k,0)` analytic inputs. The full Whittaker-type hypotheses and the supplied
additive Haar measure are retained; no uniqueness or gamma theorem is assumed.
This proposition definition does not prove the analytic inputs or covariance. -/
def UnequalRankBlockZeroContinuedFormsStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI := continuedForms_valuative_nonarchimedean (K := F)
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
      ∀ ν : AdditiveHaarMeasure F,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          let k := r - n - 1
          have hr : r = n + (0 + k + 1) := by dsimp [k]; omega
          let q := T.residueCardinality
          let abv := normalizedAbsoluteValue T
          UnequalRankAnalyticAt 0 k hr q ψ abv μ
            (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' →
          UnequalRankAnalyticAt k 0 (by omega) q (ψ.scale (-1)) abv μ
            (rectangularMeasure ν k (n + 1))
            (inverseTransposePullback π) (inverseTransposePullback σ)
            (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ') →
          UnequalRankBlockZeroContinuedFormsConclusion hnr q ψ abv μ ν π σ ℓ ℓ'

end Langlands.AllField.RankinSelberg
