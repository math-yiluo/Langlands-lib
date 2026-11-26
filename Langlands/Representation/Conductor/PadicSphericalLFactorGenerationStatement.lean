import Langlands.LocalField.Canonical
import Langlands.Representation.Conductor.SphericalLFactorGenerationStatement

/-!
# The L-factor facts behind Jacquet's existence proof, over p-adic fields

`SphericalLFactorGenerationStatement` (Jacquet 2012, section 1, printed pages 517-519)
for the field `K.Carrier` of a p-adic field `K`, with its canonical topology, valuation
and local-field structure, in place of an arbitrary nonarchimedean local field. The
binders after the field and the conclusion are those of
`SphericalLFactorGenerationStatement`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial

universe uF uV

/-- The L-factor facts of Jacquet 2012, section 1 (printed pages 517-519), over p-adic
fields. Let `K` be a p-adic field with its canonical topology, valuation and local-field
structure. Under Jacquet's normalizations `h`, let `π` be an irreducible admissible
generic representation of `GL_(n+2)(K)` and `ℓ` a nonzero `ψ`-Whittaker functional.
Then `π` has a standard L-polynomial `P` (`L(s, π × 1) = P(q^(-s))⁻¹`), and with
`W_x = W(g; x; ψ̄)`:

* for every `w` in the model of `ℓ` and every `x`, the corank-one integral
  `Ψ(s, w, W_x)` converges absolutely on a right half-plane;
* for every `w` and `x`, `Ψ(s, w, W_x) ∏ i, P(x_i q^(-s)) = q^(-Ns) Q(q^(-s))` on a
  right half-plane, for some `N : ℤ` and polynomial `Q`;
* for every `x` there are finitely many `W_j` in the model and integers `e_j` with
  `(∑_j q^(-e_j s) Ψ(s, W_j, W_x)) ∏ i, P(x_i q^(-s)) = 1` on a right half-plane. -/
def PadicSphericalLFactorGenerationStatement : Prop :=
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
      ∃ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar K.Carrier) 1 π P ∧
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
          ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule) (e : Fin k → ℤ)
            (a : ℝ),
            ∀ s : ℂ, a < s.re →
              (∑ j, spectralPoint q s ^ e j * corankOneIntegral ψ abv μ (W j).val
                  (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) *
                (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1

end Langlands.Conductor
