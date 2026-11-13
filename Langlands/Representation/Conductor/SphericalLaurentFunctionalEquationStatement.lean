import Langlands.Representation.Conductor.EssentialStatement

/-!
# The corank-one functional equation against spherical Whittaker functions, all parameters

Jacquet, Piatetski-Shapiro and Shalika 1981, (4.2)(3), printed page 209, with the
spherical test `W' = W(g; x; ψ̄)` of an unramified principal series of `GL_(n+1)`:
for every Whittaker function `W` of an irreducible generic `π` of `GL_(n+2)`,

`Ψ(1 - s, W̃, W̃') ∏ P̃(x_i⁻¹ q^(-(1-s))) = ∏ ε(s, π ⊗ χ_i, ψ) Ψ(s, W, W') ∏ P(x_i q^(-s))`,

with `ε(s, π ⊗ χ_i, ψ) = c (x_i q^(-s))^m` when `ε(s, π, ψ) = c q^(-ms)`. The
statement also records absolute convergence of both integrals on right half-planes
and that `Ψ(s, W, W') ∏ P(x_i q^(-s))` is a Laurent polynomial in `q^(-s)`
(JPSS 1983, Theorems (2.7) and (3.1)).
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

universe uF uV

/-- JPSS 1981, (4.2)(3), printed page 209, for the spherical test `W(g; x; ψ̄)`, in
rank `r = n + 2`, together with the convergence and pole bounds of JPSS 1983,
Theorems (2.7) and (3.1). Under Jacquet's normalizations `h`, with `ν` self-dual for
`ψ`, let `π` be an irreducible admissible generic representation of `GL_(n+2)(F)`,
`ℓ` a nonzero `ψ`-Whittaker functional, `L(s, π × 1) = P(q^(-s))⁻¹` and `c q^(-ms)`
the epsilon factor of `π` against the trivial character of `GL_1`. Then there is a
polynomial `Pdual` with constant term one (the L-polynomial of the contragredient)
such that for every vector `v` of the model of `ℓ` and every `x : Fin (n + 1) → ℂˣ`:

* the corank-one integral `Ψ(s, v, W(·; x; ψ̄))` and the dual integral
  `Ψ(s, ṽ, W̃(·; x; ψ̄))`, with `ṽ(g) = v(w₀ ᵗg⁻¹)` and
  `W̃(g; x; ψ̄) = W(w₀ ᵗg⁻¹; x; ψ̄)`, converge absolutely on right half-planes;
* the first continues to `Q ∏ i, P(x_i X)⁻¹` for a Laurent polynomial `Q` in
  `X = q^(-s)`, and the second to a rational function `Rdual`;
* `∏ Pdual(x_i⁻¹ q^(-(1-s))) Rdual(q^(-(1-s))) =
  c^(n+1) (∏ x_i)^m q^(-(n+1)ms) ∏ P(x_i q^(-s)) R(q^(-s))`, with
  `R = Q ∏ i, P(x_i X)⁻¹`, wherever both continuations are defined. -/
def SphericalLaurentFunctionalEquationStatement : Prop :=
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
    (ν : AdditiveHaarMeasure F), IsSelfDual ψ ν →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
      IsGeneric ψ (n + 1) π →
      ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
      ∀ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P →
      ∀ (c : ℂˣ) (m : ℤ),
        IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m) →
      ∃ Pdual : ℂ[X], Pdual.coeff 0 = 1 ∧
      ∀ (v : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          CorankOneConverges ψ abv μ v.val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) ∧
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          CorankOneConverges (ψ.scale (-1)) abv μ (firstDualFunction ψ (n + 1) v.val)
            (secondDualFunction ψ n
              (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x)) s) ∧
        ∃ (Q : LaurentPolynomial ℂ) (Rdual : RationalFunctions),
          HasRationalContinuation q
            (corankOneIntegral ψ abv μ v.val
              (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x))
            (laurentToRatFunc Q * essentialFactor P x) ∧
          HasRationalContinuation q
            (corankOneIntegral (ψ.scale (-1)) abv μ (firstDualFunction ψ (n + 1) v.val)
              (secondDualFunction ψ n
                (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x)))
            Rdual ∧
          NormalizedFunctionalEquation q (∏ i, P.comp (C (x i : ℂ) * X))
            (∏ i, Pdual.comp (C (((x i)⁻¹ : ℂˣ) : ℂ) * X)) 1
            (c ^ (n + 1) * (∏ i, x i) ^ m) (n + 1) (((n + 1 : ℕ) : ℤ) * m)
            (laurentToRatFunc Q * essentialFactor P x) Rdual

end Langlands.Conductor
