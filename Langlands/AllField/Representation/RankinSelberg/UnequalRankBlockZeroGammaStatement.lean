import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement
/-!
# The unequal-rank rational functional equation at block zero

This internal prerequisite isolates the block-zero part of JPSS Theorem 2.7.
The universal existence proposition retains the full Whittaker-type scope.
It is a statement, not a proof of existence.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBlockZeroGammaExistenceStatement UnequalRankCommonGeneratorStatement UnequalRankFunctionalEquationStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
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

/-- The same valuative-topology bridge used in `FunctionalEquationStatement`;
it supplies the additive structure required by `IsSelfDual` without a new
hypothesis on the local-field target. -/
private theorem blockZero_valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

section PadicStatement

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Existence of one nonzero rational gamma function at block zero, with the
field, topology, measures, Whittaker-type hypotheses and nonzero specified
functionals of `UnequalRankFunctionalEquationStatement`. The function `G` is
chosen before all coefficient vectors. Extending the irreducible-generic
uniqueness argument of JPSS Section 2.11 to this full scope remains a proof
obligation; no such argument is assumed here. -/
def UnequalRankBlockZeroGammaExistenceStatement (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI := blockZero_valuative_nonarchimedean (K := F)
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
          ∃ G : RationalFunctions, G ≠ 0 ∧
            UnequalRankBlockZeroGammaEquation hnr T.residueCardinality ψ
              (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' G

end PadicStatement

end Langlands.AllField.RankinSelberg
