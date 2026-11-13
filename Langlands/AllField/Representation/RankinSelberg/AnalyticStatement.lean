import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.AllField.Group.GL.Padic
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
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- Package the already proved residue-cardinality absolute value. No
base-extending spectral norm is substituted for this normalization. -/
def normalizedAbsoluteValue {F : Type uF} [Field F]
    (T : LocalFieldData F) : AbsoluteValue F ℝ where
  toFun := T.normalizedAbs
  map_mul' := T.normalizedAbs_mul
  nonneg' := T.normalizedAbs_nonneg
  eq_zero' := T.normalizedAbs_eq_zero_iff
  add_le' x y :=
    (T.normalizedAbs_add_le_max x y).trans
      (max_le (le_add_of_nonneg_right (T.normalizedAbs_nonneg y))
        (le_add_of_nonneg_left (T.normalizedAbs_nonneg x)))

@[simp] theorem normalizedAbsoluteValue_apply 
    {F : Type uF} [Field F] (T : LocalFieldData F) (x : F) :
    normalizedAbsoluteValue T x = T.normalizedAbs x := rfl

section WhittakerType

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

end WhittakerType

section EqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end EqualRank

section UnequalRank

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ} (j k : ℕ)
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end UnequalRank

section FixedRanks

variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end FixedRanks

section PadicStatements

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- JPSS Theorem 2.7(i)-(ii) for all positive unequal ranks and all rectangular
blocks. The rectangular measure is the actual product of the given additive
Haar measure. No self-dual normalization is needed until the functional equation. -/
def UnequalRankAnalyticStatement (n j k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F
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
      ∀ ν : AdditiveHaarMeasure F,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ
          (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ (n + (j + k + 1)) π)
          (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          UnequalRankAnalyticConclusion j k T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ'

/-- The same normalized reciprocal polynomial generates every allowed block
family at fixed positive ranks, as asserted in JPSS Theorem 2.7(ii). -/
def UnequalRankCommonGeneratorStatement (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  n < r →
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
          ∃ P : Polynomial ℂ, ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
            IsNormalizedGenerator
              (unequalRankValuesAt j k hr T.residueCardinality ψ
                (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1))
                π σ ℓ ℓ') P

end PadicStatements

end Langlands.AllField.RankinSelberg
