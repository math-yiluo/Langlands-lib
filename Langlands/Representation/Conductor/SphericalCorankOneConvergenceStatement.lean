import Langlands.Representation.Conductor.SphericalLFactorGenerationStatement

/-!
# Convergence of the corank-one integrals against the spherical functions

The standard L-polynomial of `π` and the absolute convergence on a right half-plane of the
corank-one integrals `Ψ(s, w, W(x; ψ̄))`, from JPSS 1983, Theorem (2.7). These are the
first two conjuncts of `SphericalLFactorGenerationStatement`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

universe uF uV

/-- JPSS 1983, Theorem (2.7), for `π × 1` and for the corank-one integrals against the
spherical functions `W(x; ψ̄)`: the first two conjuncts of
`SphericalLFactorGenerationStatement`. Under Jacquet's normalizations `h`, an irreducible
admissible generic `π` of `GL_(n+2)(F)` with a nonzero `ψ`-Whittaker functional `ℓ` has a
standard L-polynomial `P`, and for every `w` in the model of `ℓ` and every `x` the integral
`Ψ(s, w, W_x)` converges absolutely on a right half-plane. -/
def SphericalCorankOneConvergenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
    IsGeneric ψ (n + 1) π →
    ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
    ∃ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P ∧
      ∀ (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
        ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s

end Langlands.Conductor
