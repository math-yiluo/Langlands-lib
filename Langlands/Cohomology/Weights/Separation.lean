import Langlands.Cohomology.Weights.Polynomial
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# The algebraic weight-separation target

This is a proposition definition for the polynomial step in Kottwitz (1992),
Section 6. The cohomological trace identity and purity are inputs to this
algebraic implication, not asserted constructions of cohomology.
-/

noncomputable section

open Polynomial
open scoped BigOperators

universe u

namespace Langlands.Cohomology.Weights

/-- The alternating characteristic rational function for a finite list of
polynomials indexed by cohomological degree from zero through `2 * d`. -/
def alternatingPolynomial {L : Type u} [Field L] (d : ℕ)
    (H : Fin (2 * d + 1) → L[X]) : RatFunc L :=
  ∏ i, (algebraMap L[X] (RatFunc L) (H i)) ^ ((-1 : ℤ) ^ i.val)

/-- A factorization with weights indexed by degree, and the multiplicity and
parity asserted by Kottwitz's polynomial argument. -/
def IsWeightSeparation {L : Type u} [Field L] [NumberField L]
    (d q : ℕ) (w a : ℤ) (P : L[X]) (ι : L →+* ℂ)
    (H : Fin (2 * d + 1) → ℂ[X]) (Q : Fin (2 * d + 1) → L[X]) : Prop :=
  (∏ i, Q i) = P ∧
    ∀ i, IsPurePolynomial q ((i.val : ℤ) + w) (Q i) ∧
      H i = (Q i).map ι ^ a.natAbs ∧
      (((-1 : ℤ) ^ i.val) * a < 0 → Q i = 1)

/-- Separation by weights of an alternating characteristic rational function.

This is only the algebraic implication used after the geometric trace and
purity results. The factors in the conclusion are over the original number
field, so coefficient descent is a genuine part of this unproved target.
-/
def WeightSeparationStatement : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L]
    (ι : L →+* ℂ) (d q : ℕ) (w a : ℤ) (P : L[X])
    (H : Fin (2 * d + 1) → ℂ[X]),
    1 < q →
    P.Monic →
    0 < P.natDegree →
    (∀ i, (H i).Monic ∧
      ∀ z ∈ (H i).roots, IsWeilNumber q ((i.val : ℤ) + w) z) →
    alternatingPolynomial d H = (algebraMap ℂ[X] (RatFunc ℂ) (P.map ι)) ^ a →
    ((a ≠ 0 ↔ ∃ i, 0 < (H i).natDegree) ∧
      (a ≠ 0 → ∃! Q, IsWeightSeparation d q w a P ι H Q))

end Langlands.Cohomology.Weights
