import Langlands.Representation.RankinSelberg.EqualRankContinuedFormsStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
/-!
# Continued normalized equal-rank trilinear forms

This conditional statement isolates the analytic construction behind JPSS
Section 2.10. It neither proves that construction nor assumes its invariance.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- The valuative topology supplies open additive subgroups inside every
neighborhood of zero, as in the parent functional-equation scope. -/
private theorem valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

/-- Conditional construction of the two normalized continued trilinear forms.
Both have the same determinant twist at every spectral parameter, and the two
regular-point identities have separate denominator hypotheses. This is a
proposition definition, not a proof. -/
def EqualRankContinuedFormsStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI := valuative_nonarchimedean (K := F)
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
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
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          let q := T.residueCardinality
          let abv := normalizedAbsoluteValue T
          EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ' →
          EqualRankAnalyticConclusion q (ψ.scale (-1)) abv μ
            (inverseTransposePullback π) (inverseTransposePullback σ)
            (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ') →
          RowFourierClosed ψ ν (n + 1) →
          ∀ P Pdual : Polynomial ℂ,
            IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P →
            IsNormalizedGenerator (dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ') Pdual →
            let M := (coefficientModel π ℓ).toSubmodule
            let M' := (coefficientModel σ ℓ').toSubmodule
            let S := SchwartzBruhat (Fin (n + 1) → F)
            let IsTwistedInvariant :=
              fun (s : ℂ) (B : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] ℂ) =>
                ∀ (g : Langlands.GeneralLinear (n + 1) F)
                  (f : M) (f' : M') (Φ Φg : S),
                  (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) →
                    B (modelRepresentation π ℓ g f) (modelRepresentation σ ℓ' g f') Φg =
                      determinantWeight abv g (-s) * B f f' Φ
            ∃ B Bdual : ℂ → (M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] ℂ),
              (∀ s : ℂ, IsTwistedInvariant s (B s) ∧ IsTwistedInvariant s (Bdual s)) ∧
              ∀ (f : M) (f' : M') (Φ Φhat : S),
                IsRowFourierPair ψ ν Φ Φhat →
                ∀ R Rd : RationalFunctions,
                  HasRationalContinuation q
                    (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R →
                  HasRationalContinuation q
                    (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φhat) Rd →
                  ∀ s : ℂ,
                    (R.denom.eval (spectralPoint q s) ≠ 0 →
                      B s f f' Φ = P.eval (spectralPoint q s) *
                        RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) ∧
                    (Rd.denom.eval (spectralPoint q (1 - s)) ≠ 0 →
                      Bdual s f f' Φ = Pdual.eval (spectralPoint q (1 - s)) *
                        RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rd)

end Langlands.AllField.RankinSelberg
