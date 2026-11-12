import Langlands.Representation.Conductor.EssentialStatement

/-!
# The corank-one functional equation against unitary spherical functions

Jacquet, Piatetski-Shapiro and Shalika 1981, Section (4.2), display (3), printed page 209
(the specialization of display (1), printed page 208): let `π` be an irreducible generic
representation of `GL_r(F)` and `x_1, …, x_(r-1)` complex numbers of absolute value one.
For every `W` in the Whittaker model of `π`, the corank-one integral of `W` against
`W(g; x; ψ̄)` and the corank-one integral of the dual function `W̃` against
`W(g; x⁻¹; ψ)` satisfy the functional equation whose gamma factor is the product of the
rank-one gamma factors of the twists `π ⊗ χ_i`, `χ_i` unramified with `χ_i(ϖ) = x_i`.
The source derives it from JPSS 1983, Theorems (2.7) and (3.1)(i).
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

universe uF uV

/-- JPSS 1981, Section (4.2), display (3), printed page 209, in rank `r = n + 2`, for the
spherical functions `W' = W(·; x; ψ̄)` and `W̃' = W(·; x⁻¹; ψ)`. Under Jacquet's
normalizations `h` for `ψ` and `h'` for `ψ̄ = ψ.scale (-1)`, with `ν` self-dual for `ψ`:
let `π` be an irreducible admissible generic representation of `GL_(n+2)(F)`, `ℓ` a
nonzero `ψ`-Whittaker functional, `ℓ'` the dual functional of the inverse-transpose
pullback, `c q^(-ms)` the epsilon factor of `π` against the trivial character of `GL_1`,
and `P`, `P̃` the standard L-polynomials of `π` and of its inverse-transpose pullback.
For every vector `v` and every tuple `x` of complex numbers of absolute value one, the
corank-one integral of the coefficient of `v` for `ℓ` against `W(·; x; ψ̄)`, and that of
the coefficient of `v` for `ℓ'` (the dual function) against `W(·; x⁻¹; ψ)`, converge on
right half-planes and have rational continuations `R` and `R̃` with
`R̃(q^(-(1-s))) ∏ P̃(x_i⁻¹ q^(-(1-s))) = ∏ (c x_i^m q^(-ms)) · R(q^(-s)) ∏ P(x_i q^(-s))`. -/
def SphericalCorankOneFunctionalEquationStatement : Prop :=
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
      ∀ ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π),
        ℓ'.val = (dualFunctional ψ π ℓ).val →
      ∀ (c : ℂˣ) (m : ℤ),
        IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m) →
      ∀ P Pdual : ℂ[X],
        IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P →
        IsCharacterLPolynomial q (ψ.scale (-1)) abv (rankOneQuotientHaar F) 1
          (inverseTransposePullback π) Pdual →
      ∀ (v : V) (x : Fin (n + 1) → ℂˣ), (∀ i, ‖(x i : ℂ)‖ = 1) →
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          CorankOneConverges ψ abv μ (coefficientMap π ℓ v)
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) ∧
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          CorankOneConverges (ψ.scale (-1)) abv μ
            (coefficientMap (inverseTransposePullback π) ℓ' v)
            (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x⁻¹) s) ∧
        ∃ R Rdual : RationalFunctions,
          HasRationalContinuation q
            (corankOneIntegral ψ abv μ (coefficientMap π ℓ v)
              (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x)) R ∧
          HasRationalContinuation q
            (corankOneIntegral (ψ.scale (-1)) abv μ
              (coefficientMap (inverseTransposePullback π) ℓ' v)
              (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x⁻¹)) Rdual ∧
          NormalizedFunctionalEquation q
            (∏ i, P.comp (C (x i : ℂ) * X)) (∏ i, Pdual.comp (C ((x⁻¹ i : ℂˣ) : ℂ) * X))
            1 (c ^ (n + 1) * (∏ i, x i) ^ m) 0 (((n + 1 : ℕ) : ℤ) * m) R Rdual

end Langlands.Conductor
