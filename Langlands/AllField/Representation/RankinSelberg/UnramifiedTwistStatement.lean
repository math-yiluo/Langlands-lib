import Langlands.Representation.RankinSelberg.UnramifiedTwistStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-!
# Unramified twists of pair factors

Henniart 1993, §4.4 (printed page 349): twisting one member of a pair by the
unramified character `|det|^u` shifts the epsilon factor of the pair from `s`
to `s + u`. The same shift holds for the L-factor, by the substitution
`W'(h) ↦ W'(h) |det h|^u` in the Rankin-Selberg integrals of JPSS 1983.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnramifiedTwistLFactorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

/-- Twisting either member of a pair by `|det|^u`, `u ∈ ℂ`, shifts its
L-factor from `s` to `s + u`: if `L(s, π × σ) = 1 / P(q^(-s))`, then
`L(s, π × σ ⊗ |det|^u)` and `L(s, π ⊗ |det|^u × σ)` both equal
`1 / P(q^(-u) q^(-s))`. The pair is read with the larger rank first, as in
JPSS (2.12). -/
def UnramifiedTwistLFactorStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (u : ℂ) (χ : Fˣ →* ℂˣ),
    (∀ x : Fˣ,
      (χ x : ℂ) = (((⟨⟩ : LocalFieldData F).normalizedAbs (x : F) : ℝ) : ℂ) ^ u) →
    ∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
      IsPadicSymmetricLPolynomial F ψ ν.val π (Langlands.twist (χ.comp determinant) σ)
          (P.comp (C (((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ (-u)) * X)) ∧
        IsPadicSymmetricLPolynomial F ψ ν.val (Langlands.twist (χ.comp determinant) π) σ
          (P.comp (C (((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ (-u)) * X))

end Langlands.AllField.RankinSelberg
