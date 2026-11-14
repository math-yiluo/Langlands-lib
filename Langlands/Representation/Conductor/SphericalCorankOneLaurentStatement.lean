import Langlands.Representation.Conductor.SphericalLFactorGenerationStatement

/-!
# Convergence and Laurent numerators of the corank-one spherical integrals

The standard L-polynomial `P` of `π`, absolute convergence on a right half-plane of the
corank-one integrals `Ψ(s, w, W(x; ψ̄))`, and the Laurent numerator
`Ψ(s, w, W(x; ψ̄)) ∏ i, P(x_i q^(-s)) ∈ ℂ[q^(-s), q^s]`, from JPSS 1983, Theorems (2.7)
and (3.1). These are the first three conjuncts of `SphericalLFactorGenerationStatement`,
without the generation clause.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

universe uF uV

/-- JPSS 1983, Theorems (2.7) and (3.1), for `π × 1` and for the corank-one integrals
against the spherical functions `W(x; ψ̄)`: the first three conjuncts of
`SphericalLFactorGenerationStatement`. Under Jacquet's normalizations `h`, an irreducible
admissible generic `π` of `GL_(n+2)(F)` with a nonzero `ψ`-Whittaker functional `ℓ` has a
standard L-polynomial `P`, and for every `w` in the model of `ℓ` and every `x`, with
`W_x = W(g; x; ψ̄)`:

* `Ψ(s, w, W_x)` converges absolutely on a right half-plane;
* `Ψ(s, w, W_x) ∏ i, P(x_i q^(-s)) = q^(-Ns) Q(q^(-s))` on a right half-plane, for some
  `N : ℤ` and polynomial `Q`. -/
def SphericalCorankOneLaurentStatement : Prop :=
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
      (∀ (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
        ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) ∧
      ∀ (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
        ∃ (a : ℝ) (N : ℤ) (Q : ℂ[X]), ∀ s : ℂ, a < s.re →
          corankOneIntegral ψ abv μ w.val
              (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s *
            (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
          spectralPoint q s ^ N * Q.eval (spectralPoint q s)

end Langlands.Conductor
