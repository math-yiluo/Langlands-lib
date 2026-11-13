import Langlands.Representation.Conductor.EssentialStatement

/-!
# The L-factor facts behind Jacquet's existence proof

Jacquet 2012, section 1 (printed pages 517-519), recalls from Jacquet,
Piatetski-Shapiro and Shalika 1983 the facts about the corank-one integrals
`Ψ(s, W, W(x; ψ̄))` that his proof of the existence of the essential vector uses. Let
`π` be an irreducible admissible generic representation of `GL_(n+2)(F)` with standard
L-polynomial `P`. For every Whittaker function `W` of `π` and every Satake parameter `x`
the integral converges on a right half-plane, its product with `∏ P(x_i q^(-s))` is a
Laurent polynomial in `q^(-s)`, and (Jacquet's Lemma 4) a finite sum
`∑_j q^(-n_j s) Ψ(s, W_j, W(x; ψ̄))` equals `∏ P(x_i q^(-s))⁻¹`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

universe uF uV

/-- The L-factor facts of Jacquet 2012, section 1 (printed pages 517-519), taken from
JPSS 1983, Theorems (2.7) and (3.1), together with Jacquet's Lemma 4. Under Jacquet's
normalizations `h`, let `π` be an irreducible admissible generic representation of
`GL_(n+2)(F)` and `ℓ` a nonzero `ψ`-Whittaker functional. Then `π` has a standard
L-polynomial `P` (`L(s, π × 1) = P(q^(-s))⁻¹`), and with `W_x = W(g; x; ψ̄)`:

* for every `w` in the model of `ℓ` and every `x`, the corank-one integral
  `Ψ(s, w, W_x)` converges absolutely on a right half-plane;
* for every `w` and `x`, `Ψ(s, w, W_x) ∏ i, P(x_i q^(-s)) = q^(-Ns) Q(q^(-s))` on a
  right half-plane, for some `N : ℤ` and polynomial `Q`;
* for every `x` there are finitely many `W_j` in the model and integers `e_j` with
  `(∑_j q^(-e_j s) Ψ(s, W_j, W_x)) ∏ i, P(x_i q^(-s)) = 1` on a right half-plane. -/
def SphericalLFactorGenerationStatement : Prop :=
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
      (∀ (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
        ∃ (a : ℝ) (N : ℤ) (Q : ℂ[X]), ∀ s : ℂ, a < s.re →
          corankOneIntegral ψ abv μ w.val
              (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s *
            (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
          spectralPoint q s ^ N * Q.eval (spectralPoint q s)) ∧
      ∀ x : Fin (n + 1) → ℂˣ,
        ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule) (e : Fin k → ℤ) (a : ℝ),
          ∀ s : ℂ, a < s.re →
            (∑ j, spectralPoint q s ^ e j * corankOneIntegral ψ abv μ (W j).val
                (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) *
              (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1

end Langlands.Conductor
