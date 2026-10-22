import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.RationalZeta
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalFactor.Euler

/-!
# JPSS convergence and rationality on actual coefficient models

These are proposition definitions, not proofs of the JPSS analytic theorem.
The quotient measure is any measure satisfying the published compatibility
predicate `QuotientIntegration.IsCompatible`; its existence is a separate
proposition. The scope is admissible finite-type Whittaker type, including
reducible representations.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The complex spectral point agrees with the shared nonzero exponential
parameter. The positive real cardinality proof affects no value. -/
theorem spectralPoint_eq_spectralParameter (q : ℕ) (hq : 0 < (q : ℝ)) (s : ℂ) :
    spectralPoint q s = (LocalFactor.spectralParameter (q : ℝ) hq s : ℂ) := by
  simpa only [spectralPoint, Complex.ofReal_natCast] using
    (LocalFactor.spectralParameter_eq_cpow (q : ℝ) hq s).symm

/-- Package the already proved residue-cardinality absolute value. No
base-extending spectral norm is substituted for this normalization. -/
def normalizedAbsoluteValue {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) : AbsoluteValue F.Carrier ℝ where
  toFun := T.normalizedAbs
  map_mul' := T.normalizedAbs_mul
  nonneg' := T.normalizedAbs_nonneg
  eq_zero' := T.normalizedAbs_eq_zero_iff
  add_le' x y :=
    (T.normalizedAbs_add_le_max x y).trans
      (max_le (le_add_of_nonneg_right (T.normalizedAbs_nonneg y))
        (le_add_of_nonneg_left (T.normalizedAbs_nonneg x)))

@[simp] theorem normalizedAbsoluteValue_apply {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) (x : F.Carrier) :
    normalizedAbsoluteValue T x = T.normalizedAbs x := rfl

section WhittakerType

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- JPSS Section 2.1: admissibility, finite generation over the group algebra,
and an exactly one-dimensional space of functionals for the specified character.
This does not assume irreducibility or finite-dimensionality of the representation. -/
def IsOfWhittakerType (n : ℕ) (θ : upperUnipotent (n + 1) F →* ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) : Prop :=
  IsAdmissible π ∧
  Module.Finite (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F)) π.asModule ∧
  Nonempty ((functionals (upperUnipotent (n + 1) F) θ π) ≃ₗ[ℂ] ℂ)

end WhittakerType

section EqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Rational continuations of actual equal-rank coefficient-model integrals.
No rationality is assumed when this set is defined. -/
def equalRankRationalValues (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) :
    Set RationalFunctions :=
  {R | ∃ f : (coefficientModel π ℓ).toSubmodule,
    ∃ f' : (coefficientModel σ ℓ').toSubmodule,
    ∃ Φ : SchwartzBruhat (Fin (n + 1) → F),
      HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R}

/-- Equal-rank convergence, rational continuation, fractional-ideal boundedness,
and existence of the normalized reciprocal-polynomial generator. -/
def EqualRankAnalyticConclusion (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) : Prop :=
  (∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
    ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
      ∃ a : ℝ, ∀ s : ℂ, a < s.re →
        EqualRankConverges ψ abv μ f.val f'.val Φ s) ∧
  (∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
    ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
      ∃ R : RationalFunctions,
        HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R) ∧
  HasCommonDenominator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') ∧
  NormalizedGeneratorExists (equalRankRationalValues q ψ abv μ π σ ℓ ℓ')

end EqualRank

section UnequalRank

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ} (j k : ℕ)
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Rational continuations of the specified actual unequal-rank block family. -/
def unequalRankRationalValues (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ) :
    Set RationalFunctions :=
  {R | ∃ f : (coefficientModel π ℓ).toSubmodule,
    ∃ f' : (coefficientModel σ ℓ').toSubmodule,
      HasRationalContinuation q
        (unequalRankModelIntegral ψ abv j k μ ν π σ ℓ ℓ' f f') R}

/-- All allowed unequal-rank blocks have convergent, rational integrals and
a normalized generator. Independence of the chosen block is a separate target. -/
def UnequalRankAnalyticConclusion (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ) : Prop :=
  (∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
      ∃ a : ℝ, ∀ s : ℂ, a < s.re →
        UnequalRankConverges ψ abv j k μ ν f.val f'.val s) ∧
  (∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
      ∃ R : RationalFunctions, HasRationalContinuation q
        (unequalRankModelIntegral ψ abv j k μ ν π σ ℓ ℓ' f f') R) ∧
  HasCommonDenominator (unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ') ∧
  NormalizedGeneratorExists (unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ')

end UnequalRank

section FixedRanks

variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The same actual rational-value set with the large rank fixed independently
of the block index. Equality of natural-number ranks transports only types. -/
def unequalRankValuesAt (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    Set RationalFunctions := by
  subst r
  exact unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ'

end FixedRanks

section PadicStatements

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Existence of a quotient measure on each actual left-unipotent quotient
`N_(n+1) \ GL_(n+1)`, compatible with the normalized Haar measures of
`RankinSelberg.Measures`. Right invariance of the unipotent Haar measure,
which the published compatibility predicate presupposes, is part of the claim.
No representation or zeta integral occurs. -/
def QuotientHaarExistenceStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∃ _ : Measure.IsMulRightInvariant (unipotentHaar F.Carrier n),
    CompatibleMeasureExists (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n)

/-- JPSS Theorem 2.7(i)-(ii), equal rank, over every specified p-adic field.
Every character, representation, nonzero functional and compatible quotient
measure is quantified explicitly. -/
def EqualRankAnalyticStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
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
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          EqualRankAnalyticConclusion T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ π σ ℓ ℓ'

/-- JPSS Theorem 2.7(i)-(ii) for all positive unequal ranks and all rectangular
blocks. The rectangular measure is the actual product of the given additive
Haar measure. No self-dual normalization is needed until the functional equation. -/
def UnequalRankAnalyticStatement (n j k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
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
      ∀ ν : AdditiveHaarMeasure F.Carrier,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ
          (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
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
  letI := borel F.Carrier
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  n < r →
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
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

end Langlands.RankinSelberg
