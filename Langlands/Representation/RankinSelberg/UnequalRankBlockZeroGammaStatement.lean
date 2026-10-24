import Langlands.Representation.RankinSelberg.GammaFactor

/-!
# The unequal-rank rational functional equation at block zero

This internal prerequisite isolates the block-zero part of JPSS Theorem 2.7.
The universal existence proposition retains the full Whittaker-type scope.
It is a statement, not a proof of existence.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section FixedData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The literal block-zero restriction of `UnequalRankGammaEquation`.
The minus-one scalar and a nonzero original rational value exist, and the same
`G` relates every pair of actual coefficient-model integrals to its transformed
complementary-block integral. Nonvanishing of `G` is imposed by the universal
existence statement below. -/
def UnequalRankBlockZeroGammaEquation (hnr : n < r)
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
    (G : RationalFunctions) : Prop :=
  let k := r - n - 1
  have hr : r = n + (0 + k + 1) := by dsimp [k]; omega
  ∃ ζ : ℂˣ, HasModelMinusOneScalar σ ℓ' ζ ∧
    (∃ R ∈ unequalRankValuesAt 0 k hr q ψ abv μ (rectangularMeasure ν 0 (n + 1))
      π σ ℓ ℓ', R ≠ 0) ∧
    ∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
      ∃ R Rdual : RationalFunctions,
        HasRationalContinuation q
          (unequalRankIntegralAt 0 k hr ψ abv μ (rectangularMeasure ν 0 (n + 1))
            f.val f'.val) R ∧
        HasRationalContinuation q
          (dualUnequalRankModelIntegralAt hnr 0 k hr ψ abv μ ν π σ ℓ ℓ' f f') Rdual ∧
        GammaFunctionalEquation q ζ r G R Rdual

end FixedData

/-- The same valuative-topology bridge used in `FunctionalEquationStatement`;
it supplies the additive structure required by `IsSelfDual` without a new
hypothesis on the p-adic target. -/
private theorem blockZero_valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

section PadicStatement

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

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
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := blockZero_valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ hnr : n < r,
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier, IsSelfDual ψ ν →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∃ G : RationalFunctions, G ≠ 0 ∧
            UnequalRankBlockZeroGammaEquation hnr T.residueCardinality ψ
              (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' G

end PadicStatement

end Langlands.RankinSelberg
