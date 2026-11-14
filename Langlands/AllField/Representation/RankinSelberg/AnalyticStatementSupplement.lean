import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.AllField.Group.GL.PadicSupplement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# JPSS convergence and rationality on actual coefficient models

These are proposition definitions, not proofs of the JPSS analytic theorem.
The quotient measure is any measure satisfying the published compatibility
predicate `QuotientIntegration.IsCompatible`; its existence is a separate
proposition. The scope is admissible finite-type Whittaker type, including
reducible representations.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section WhittakerType


end WhittakerType

section EqualRank


end EqualRank

section UnequalRank


end UnequalRank

section FixedRanks


end FixedRanks

section PadicStatements

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Existence of a quotient measure on each actual left-unipotent quotient
`N_(n+1) \ GL_(n+1)`, compatible with the normalized Haar measures of
`RankinSelberg.Measures`. Right invariance of the unipotent Haar measure,
which the published compatibility predicate presupposes, is part of the claim.
No representation or zeta integral occurs. -/
def QuotientHaarExistenceStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  ∃ _ : Measure.IsMulRightInvariant (unipotentHaar F n),
    CompatibleMeasureExists (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n)

/-- JPSS Theorem 2.7(i)-(ii), equal rank, over every specified p-adic field.
Every character, representation, nonzero functional and compatible quotient
measure is quantified explicitly. -/
def EqualRankAnalyticStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          EqualRankAnalyticConclusion T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ π σ ℓ ℓ'

end PadicStatements

end Langlands.AllField.RankinSelberg
