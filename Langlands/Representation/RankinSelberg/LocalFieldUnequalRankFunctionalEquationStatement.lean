import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.Whittaker.Iwasawa

/-!
# The unequal-rank JPSS functional equation over every nonarchimedean local field

Jacquet, Piatetski-Shapiro and Shalika 1983, Theorem (2.7)(iii) (printed pages
390–391), for a pair of ranks `r + 1 > n + 1`, over an arbitrary nonarchimedean local
field `F` (any characteristic). The conclusion is the published
`UnequalRankFunctionalEquationConclusion`, the same one that the p-adic
`UnequalRankFunctionalEquationStatement` uses. This module contains no proof.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open Langlands.GeneralLinear.Iwasawa

universe uF uV uW

/-- JPSS 1983, Theorem (2.7)(iii), printed pages 390–391, for unequal ranks
`r + 1 > n + 1`, over every nonarchimedean local field `F` with Borel structures.
`q` is the residue cardinality and `abv` the normalized absolute value
(`abv ϖ = q⁻¹` for a uniformizer `ϖ`, `abv x = 1` on valuation units). For every
additive character `ψ`, every compatible quotient measure `μ`, every `ν` self-dual for
`ψ`, every `π` of `GL_(r+1)(F)` of Whittaker type for the standard character, every `σ`
of `GL_(n+1)(F)` of Whittaker type for the inverse standard character and every pair of
nonzero functionals, one scalar `ζ`, one epsilon monomial `c X^m` and one pair of
normalized generator polynomials satisfy the normalized functional equation for every
complementary block `r = n + (j + k + 1)`. -/
def LocalFieldUnequalRankFunctionalEquationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F] (n r : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
    (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
    ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
      abv (ϖ : F) = (q : ℝ)⁻¹ → (∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) →
    ∀ (hnr : n < r) (ψ : UnitaryAdditiveCharacter F),
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ →
    ∀ ν : AdditiveHaarMeasure F, IsSelfDual ψ ν →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsOfWhittakerType r (standardCharacter ψ r) π →
      IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
      ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        UnequalRankFunctionalEquationConclusion hnr q ψ abv μ ν π σ ℓ ℓ'

end Langlands.RankinSelberg
