import Langlands.Representation.RankinSelberg.UnequalRankGammaFactor
import Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement

/-!
# Continued unequal-rank bilinear forms at block zero

This conditional interface isolates the construction of the actual continued
integrals with the covariance of JPSS (2.11.2) and (2.11.4). It states neither
analytic continuation existence nor bilinear uniqueness nor gamma existence.
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

/-- Unnormalized original and reflected dual continued values give covariant
bilinear forms outside one finite set of spectral values. Each evaluation
clause separately quantifies over all continuations of its actual integral. -/
def UnequalRankBlockZeroContinuedFormsConclusion (hnr : n < r)
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) : Prop :=
  let k := r - n - 1
  have hr : r = n + (0 + k + 1) := by dsimp [k]; omega
  let M := (coefficientModel π ℓ).toSubmodule
  let M' := (coefficientModel σ ℓ').toSubmodule
  ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
    ∃ B Bdual : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ,
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B ∧
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s Bdual ∧
      (∀ (f : M) (f' : M') (R : RationalFunctions),
        HasRationalContinuation q
          (unequalRankIntegralAt 0 k hr ψ abv μ (rectangularMeasure ν 0 (n + 1))
            f.val f'.val) R →
          R.denom.eval (spectralPoint q s) ≠ 0 ∧
          B f f' = RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) ∧
      (∀ (f : M) (f' : M') (Rd : RationalFunctions),
        HasRationalContinuation q
          (dualUnequalRankModelIntegralAt hnr 0 k hr ψ abv μ ν π σ ℓ ℓ' f f') Rd →
          Rd.denom.eval (spectralPoint q (1 - s)) ≠ 0 ∧
          Bdual f f' = RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rd)

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
def UnequalRankBlockZeroContinuedFormsStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := continuedForms_valuative_nonarchimedean (K := F.Carrier)
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
      ∀ ν : AdditiveHaarMeasure F.Carrier,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
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

end Langlands.RankinSelberg
