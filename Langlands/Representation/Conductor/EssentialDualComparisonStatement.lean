import Langlands.Representation.Conductor.EssentialStatement

/-!
# Comparison of the dual essential vector with a translated dual essential vector

Jacquet, Piatetski-Shapiro and Shalika 1981, Section (5.3), printed page 213: if `W`
is the essential vector of `π`, `W'` the essential vector of the dual model and
`c q^(-ms)` the epsilon factor of `π`, then the dual function `W̃` is a constant
multiple of the right translate `g ↦ W'(g a)` with `a = diag(ϖ^m, ..., ϖ^m, 1)`.
The essential vectors are the corrected ones of Jacquet 2012, Theorem 1.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory

universe uF uV

/-- JPSS 1981, Section (5.3), printed page 213, in rank `r = n + 2`. Under Jacquet's
normalizations `h` for `ψ` and `h'` for `ψ̄ = ψ.scale (-1)`, with `ν` self-dual for
`ψ`: let `w` be an essential vector of the model of a nonzero `ψ`-Whittaker functional
`ℓ` of an irreducible admissible generic `π` of `GL_(n+2)(F)`, let `w'` be an essential
vector of the model of the dual functional `ℓ'` of the inverse-transpose pullback of
`π`, and let `c q^(-ms)` (`m : ℤ`) be the epsilon factor of `π` against the trivial
character of `GL_1`. Then some constant `C` satisfies
`W̃(g) = C · w'(g · diag(ϖ^m, ..., ϖ^m, 1))` for every `g ∈ GL_(n+2)(F)`. -/
def EssentialDualComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    (h' : IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ)
    (ν : AdditiveHaarMeasure F), IsSelfDual ψ ν →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
      IsGeneric ψ (n + 1) π →
      ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
      ∀ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w →
      ∀ ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π),
        ℓ'.val = (dualFunctional ψ π ℓ).val →
      ∀ w' : (coefficientModel (inverseTransposePullback π) ℓ').toSubmodule,
        IsEssentialVector h' (inverseTransposePullback π) ℓ' w' →
      ∀ (c : ℂˣ) (m : ℤ),
        IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m) →
        ∃ C : ℂ, ∀ g : Langlands.GeneralLinear ((n + 1) + 1) F,
          dualFunction (n + 1) w.val.val g =
            C * w'.val.val (g * rankInclusion 1 (scalar (ϖ ^ m)))

end Langlands.Conductor
