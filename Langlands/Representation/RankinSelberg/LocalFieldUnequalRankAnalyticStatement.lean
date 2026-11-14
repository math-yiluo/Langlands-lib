import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Whittaker.Iwasawa

/-!
# Unequal-rank convergence and rationality over every nonarchimedean local field

Jacquet, Piatetski-Shapiro and Shalika 1983, Theorem (2.7)(i)–(ii) (printed page 390),
for a pair of ranks `n + (j + k + 1) + 1 > n + 1` and the rectangular block `j, k`, over
an arbitrary nonarchimedean local field `F` (any characteristic). The conclusion is the
published `UnequalRankAnalyticConclusion`, the same one that the p-adic
`UnequalRankAnalyticStatement` uses. This module contains no proof.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open Langlands.GeneralLinear.Iwasawa

universe uF uV uW

/-- JPSS 1983, Theorem (2.7)(i)–(ii), printed page 390, for the block `j, k` of the
unequal ranks `n + (j + k + 1) + 1 > n + 1`, over every nonarchimedean local field `F`
with Borel structures. `q` is the residue cardinality and `abv` the normalized absolute
value (`abv ϖ = q⁻¹` for a uniformizer `ϖ`, `abv x = 1` on valuation units). For every
additive character `ψ`, every compatible quotient measure `μ`, every additive Haar
measure `ν`, every `π` of Whittaker type for the standard character, every `σ` of
Whittaker type for the inverse standard character and every pair of nonzero functionals,
the block integrals converge absolutely on a right half-plane, have rational
continuations, admit a common denominator and have a normalized generator. -/
def LocalFieldUnequalRankAnalyticStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F] (n j k : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
    (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
    ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
      abv (ϖ : F) = (q : ℝ)⁻¹ → (∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) →
    ∀ (ψ : UnitaryAdditiveCharacter F),
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ →
    ∀ ν : AdditiveHaarMeasure F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π →
      IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
      ∀ (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        UnequalRankAnalyticConclusion j k q ψ abv μ (rectangularMeasure ν j (n + 1))
          π σ ℓ ℓ'

end Langlands.RankinSelberg
