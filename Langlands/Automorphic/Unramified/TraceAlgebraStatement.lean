import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Basic.Complex.Basic

/-!
Algebraic prerequisites for the unramified trace formulation of automorphic
rigidity and cyclic transfer. These are proposition definitions, not proofs.
The matrices and determinant polynomials are actual Mathlib objects.
No automorphic or Satake object is postulated here.
-/

open scoped BigOperators
open Polynomial

namespace Langlands.Automorphic.Unramified

/-- Equality of products of normalized determinant polynomials is equivalent
to equality of the sums of all positive power traces, with varying ranks. -/
def EulerProductTraceStatement : Prop :=
  ∀ (a b : ℕ) (n : Fin a → ℕ) (m : Fin b → ℕ)
    (A : (i : Fin a) → Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (B : (j : Fin b) → Matrix (Fin (m j)) (Fin (m j)) ℂ),
    (∏ i, (A i).charpolyRev) = (∏ j, (B j).charpolyRev) ↔
      ∀ k : ℕ, 0 < k →
        (∑ i, Matrix.trace ((A i) ^ k)) =
          (∑ j, Matrix.trace ((B j) ^ k))

/-- The determinant-polynomial formula for unramified induction, expressed
equivalently by power traces. Each `f i` is a positive residue-degree input;
this algebraic statement does not assert that it comes from a field extension. -/
def InductionPolynomialTraceStatement : Prop :=
  ∀ (a m : ℕ) (n f : Fin a → ℕ)
    (A : (i : Fin a) → Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ),
    (∀ i, 0 < f i) →
      ((B.charpolyRev = ∏ i, (A i).charpolyRev.comp (X ^ f i)) ↔
        ∀ k : ℕ, 0 < k →
          Matrix.trace (B ^ k) =
            ∑ i, if f i ∣ k then
              (f i : ℂ) * Matrix.trace ((A i) ^ (k / f i)) else 0)

/-- Nonzero determinants ensure that the degree of the induced normalized
polynomial is the full sum of residue degrees times matrix ranks. -/
def InductionPolynomialDegreeStatement : Prop :=
  ∀ (a : ℕ) (n f : Fin a → ℕ)
    (A : (i : Fin a) → Matrix (Fin (n i)) (Fin (n i)) ℂ),
    (∀ i, 0 < f i) → (∀ i, (A i).det ≠ 0) →
      (∏ i, (A i).charpolyRev.comp (X ^ f i)).natDegree =
        ∑ i, f i * n i

/-- The complete algebraic prerequisite group. It neither asserts the
Jacquet-Shalika linear-independence theorem nor the existence of a transfer. -/
def TraceAlgebraStatement : Prop :=
  EulerProductTraceStatement ∧
    InductionPolynomialTraceStatement ∧
      InductionPolynomialDegreeStatement

end Langlands.Automorphic.Unramified
