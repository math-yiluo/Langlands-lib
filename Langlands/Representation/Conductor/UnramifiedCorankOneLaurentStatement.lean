import Langlands.Representation.Conductor.SphericalLFactorGenerationStatement
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries

/-!
# Laurent numerators of the corank-one integrals of `π × I(x)`

JPSS 1983, Theorem (3.1)(ii), for the corank-one integrals of `π × I(x)`, where `I(x)` is
the normalized unramified principal series: every integral times `∏ i, P(x_i q^(-s))` is a
Laurent polynomial in `q^(-s)`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF uV

/-- JPSS 1983, Theorem (3.1)(ii) (with Theorem (2.7)), for the normalized unramified
principal series. Under Jacquet's normalizations `h`, let `π` be an irreducible admissible
generic representation of `GL_(n+2)(F)` with nonzero `ψ`-Whittaker functional `ℓ` and
standard L-polynomial `P`, let `x : Fin (n + 1) → ℂˣ` be arbitrary, and let `ℓ'` be a
nonzero `ψ̄`-Whittaker functional on the normalized unramified principal series `I(x)`.
Then for `W` in the model of `ℓ` and `W'` in the model of `ℓ'` whose integral
`Ψ(s, W, W')` converges absolutely on a right half-plane, the product
`Ψ(s, W, W') ∏ i, P(x_i q^(-s))` is `q^(-Ns) Q(q^(-s))` on a right half-plane, for some
`N : ℤ` and polynomial `Q`. With `x_i = q^(-t_i)`: every corank-one integral of
`π × I(x)` lies in `∏ i, L(s + t_i, π) · ℂ[q^(-s), q^s]`. -/
def UnramifiedCorankOneLaurentStatement : Prop :=
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
    ∀ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P →
    ∀ x : Fin (n + 1) → ℂˣ,
    ∀ ℓ' : glInverseFunctionals ψ n
        (principalSeries h.uniformizer n h.residueCardinality x), ℓ'.val ≠ 0 →
    ∀ (W : (coefficientModel π ℓ).toSubmodule)
        (W' : (coefficientModel
          (principalSeries h.uniformizer n h.residueCardinality x) ℓ').toSubmodule),
      (∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ W.val W'.val s) →
      ∃ (a : ℝ) (N : ℤ) (Q : ℂ[X]), ∀ s : ℂ, a < s.re →
        corankOneIntegral ψ abv μ W.val W'.val s *
            (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
          spectralPoint q s ^ N * Q.eval (spectralPoint q s)

end Langlands.Conductor
