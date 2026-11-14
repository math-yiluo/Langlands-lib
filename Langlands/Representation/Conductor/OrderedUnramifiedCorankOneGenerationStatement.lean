import Langlands.Representation.Conductor.SphericalLFactorGenerationStatement
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries

/-!
# Generation of `∏ L(s + t_i, π)` by corank-one integrals of `π × I(x)`, ordered `x`

Jacquet 2012, Lemma 3 (printed page 519), quoted from JPSS 1983, for the corank-one
integrals of `π × I(x)`, where `I(x)` is the normalized unramified principal series with
norm-ordered Satake parameters: a finite sum of integrals equals `∏ i, P(x_i q^(-s))⁻¹`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF uV

/-- Jacquet 2012, Lemma 3 (printed page 519), quoted from JPSS 1983, for the normalized
unramified principal series with norm-ordered parameters. Under Jacquet's normalizations
`h`, let `π` be an irreducible admissible generic representation of `GL_(n+2)(F)` with
nonzero `ψ`-Whittaker functional `ℓ` and standard L-polynomial `P`, let `x` have
nondecreasing norms `|x_1| ≤ ⋯ ≤ |x_(n+1)|`, and let `ℓ'` be a nonzero `ψ̄`-Whittaker
functional on the normalized unramified principal series `I(x)`. Then finitely many `W_j`
in the model of `ℓ` and `W'_j` in the model of `ℓ'` satisfy
`(∑_j Ψ(s, W_j, W'_j)) ∏ i, P(x_i q^(-s)) = 1` on a right half-plane. With
`x_i = q^(-t_i)`: `∑_j Ψ(s, W_j, W'_j) = ∏ i, L(s + t_i, π)`. -/
def OrderedUnramifiedCorankOneGenerationStatement : Prop :=
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
    ∀ x : Fin (n + 1) → ℂˣ, Monotone (fun i => ‖(x i : ℂ)‖) →
    ∀ ℓ' : glInverseFunctionals ψ n
        (principalSeries h.uniformizer n h.residueCardinality x), ℓ'.val ≠ 0 →
      ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule)
        (W' : Fin k → (coefficientModel
          (principalSeries h.uniformizer n h.residueCardinality x) ℓ').toSubmodule) (a : ℝ),
        ∀ s : ℂ, a < s.re →
          (∑ j, corankOneIntegral ψ abv μ (W j).val (W' j).val s) *
            (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1

end Langlands.Conductor
