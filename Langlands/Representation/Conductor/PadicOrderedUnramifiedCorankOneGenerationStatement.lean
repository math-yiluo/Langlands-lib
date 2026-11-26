import Langlands.LocalField.Canonical
import Langlands.Representation.Conductor.OrderedUnramifiedCorankOneGenerationStatement

/-!
# Generation of `∏ L(s + t_i, π)` by corank-one integrals of `π × I(x)`, over p-adic fields

`OrderedUnramifiedCorankOneGenerationStatement` (Jacquet 2012, Lemma 3, printed page
519, quoted from JPSS 1983) for the field `K.Carrier` of a p-adic field `K`, with its
canonical topology, valuation and local-field structure, in place of an arbitrary
nonarchimedean local field. The binders after the field and the conclusion are those of
`OrderedUnramifiedCorankOneGenerationStatement`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF uV

/-- Jacquet 2012, Lemma 3 (printed page 519), quoted from JPSS 1983, over p-adic fields,
for the normalized unramified principal series with norm-ordered parameters. Let `K` be
a p-adic field with its canonical topology, valuation and local-field structure. Under
Jacquet's normalizations `h`, let `π` be an irreducible admissible generic
representation of `GL_(n+2)(K)` with nonzero `ψ`-Whittaker functional `ℓ` and standard
L-polynomial `P`, let `x` have nondecreasing norms `|x_1| ≤ ⋯ ≤ |x_(n+1)|`, and let `ℓ'`
be a nonzero `ψ̄`-Whittaker functional on the normalized unramified principal series
`I(x)`. Then finitely many `W_j` in the model of `ℓ` and `W'_j` in the model of `ℓ'`
satisfy `(∑_j Ψ(s, W_j, W'_j)) ∏ i, P(x_i q^(-s)) = 1` on a right half-plane. With
`x_i = q^(-t_i)`: `∑_j Ψ(s, W_j, W'_j) = ∏ i, L(s + t_i, π)`. -/
def PadicOrderedUnramifiedCorankOneGenerationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p),
    letI := K.canonicalTopologicalData.topology
    letI := K.canonicalTopologicalData.valuativeRel
    letI := K.canonicalTopologicalData.localField
    ∀ (n : ℕ)
      [MeasurableSpace (Langlands.GeneralLinear (n + 1) K.Carrier)]
      [BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier)]
      [MeasurableSpace (upperUnipotent (n + 1) K.Carrier)]
      [BorelSpace (upperUnipotent (n + 1) K.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient n K.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient 0 K.Carrier)]
      [MeasurableSpace (Langlands.GeneralLinear 1 K.Carrier)]
      [BorelSpace (Langlands.GeneralLinear 1 K.Carrier)]
      (q : ℕ) (ψ : UnitaryAdditiveCharacter K.Carrier) (abv : AbsoluteValue K.Carrier ℝ)
      (ϖ : K.Carrierˣ) (μ : Measure (LeftUnipotentQuotient n K.Carrier))
      (h : IsJacquetNormalization q ψ abv ϖ μ)
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) K.Carrier) V),
      IsGeneric ψ (n + 1) π →
      ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
      ∀ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar K.Carrier) 1 π P →
      ∀ x : Fin (n + 1) → ℂˣ, Monotone (fun i => ‖(x i : ℂ)‖) →
      ∀ ℓ' : glInverseFunctionals ψ n
          (principalSeries h.uniformizer n h.residueCardinality x), ℓ'.val ≠ 0 →
        ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule)
          (W' : Fin k → (coefficientModel
            (principalSeries h.uniformizer n h.residueCardinality x) ℓ').toSubmodule)
          (a : ℝ),
          ∀ s : ℂ, a < s.re →
            (∑ j, corankOneIntegral ψ abv μ (W j).val (W' j).val s) *
              (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1

end Langlands.Conductor
