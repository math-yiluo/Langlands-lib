import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial isolation of a submodule

Filtration-step annihilators give one polynomial taking the whole module into
its distinguished submodule. A polynomial Bezout identity then gives a linear
map into that submodule whose restriction is multiplication by one scalar.
Resultants supply such identities over arbitrary commutative rings.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Langlands.Plancherel.PolynomialIsolation

universe uR uV

variable {R : Type uR} [CommRing R]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- A product of step annihilators takes the last filtration term into the
first. The step assumptions are on the actual ambient module. -/
theorem aeval_prod_range_mem
    (T : Module.End R V) (F : ℕ → Submodule R V) (p : ℕ → R[X])
    (n : ℕ)
    (hstep : ∀ i < n, ∀ v ∈ F (i + 1), aeval T (p i) v ∈ F i)
    (v : V) (hv : v ∈ F n) :
    aeval T (∏ i ∈ Finset.range n, p i) v ∈ F 0 := by
  induction n generalizing v with
  | zero => simpa using hv
  | succ n ih =>
    rw [Finset.prod_range_succ, aeval_mul, Module.End.mul_apply]
    exact ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      _ (hstep n (Nat.lt_succ_self n) v hv)

/-- If the first term is bottom, the filtration product kills the last term. -/
theorem aeval_prod_range_eq_zero
    (T : Module.End R V) (F : ℕ → Submodule R V) (p : ℕ → R[X])
    (n : ℕ) (hzero : F 0 = ⊥)
    (hstep : ∀ i < n, ∀ v ∈ F (i + 1), aeval T (p i) v ∈ F i)
    (v : V) (hv : v ∈ F n) :
    aeval T (∏ i ∈ Finset.range n, p i) v = 0 := by
  have h := aeval_prod_range_mem T F p n hstep v hv
  simpa only [hzero, Submodule.mem_bot] using h

/-- A polynomial taking every vector into `U` still does so after multiplication
by any second polynomial. No stability hypothesis on `U` is needed. -/
def polynomialRangeMap
    (T : Module.End R V) (U : Submodule R V) (q b : R[X])
    (hq : ∀ v, aeval T q v ∈ U) : V →ₗ[R] U :=
  (aeval T (q * b)).codRestrict U (fun v => by
    rw [aeval_mul, Module.End.mul_apply]
    exact hq _)

@[simp]
theorem polynomialRangeMap_apply
    (T : Module.End R V) (U : Submodule R V) (q b : R[X])
    (hq : ∀ v, aeval T q v ∈ U) (v : V) :
    (polynomialRangeMap T U q b hq v : V) = aeval T (q * b) v := rfl

/-- The Bezout map restricts to the scalar in the Bezout identity. Commutativity
of polynomials permits the annihilator to be applied before its multiplier. -/
theorem polynomialRangeMap_eq_smul
    (T : Module.End R V) (U : Submodule R V) (p q a b : R[X]) (c : R)
    (hp : ∀ v ∈ U, aeval T p v = 0)
    (hq : ∀ v, aeval T q v ∈ U)
    (hbezout : p * a + q * b = C c) (u : U) :
    polynomialRangeMap T U q b hq u = c • u := by
  apply Subtype.ext
  change aeval T (q * b) (u : V) = c • (u : V)
  have hpa : aeval T (p * a) (u : V) = 0 := by
    rw [mul_comm p a, aeval_mul, Module.End.mul_apply, hp u u.property, map_zero]
  have h := congrArg (fun f : R[X] => aeval T f (u : V)) hbezout
  simpa only [aeval_add, LinearMap.add_apply, hpa, zero_add, aeval_C,
    Module.algebraMap_end_apply] using h

/-- Resultant Bezout identities provide a polynomial range map whose
restriction to `U` is the same scalar on every vector of `U`. -/
theorem exists_resultant_polynomialRangeMap
    (T : Module.End R V) (U : Submodule R V) (p q : R[X])
    {m n : ℕ} (hpdeg : p.natDegree ≤ m) (hqdeg : q.natDegree ≤ n)
    (hdegree : m ≠ 0 ∨ n ≠ 0)
    (hp : ∀ v ∈ U, aeval T p v = 0)
    (hq : ∀ v, aeval T q v ∈ U) :
    ∃ b : R[X], ∀ u : U,
      polynomialRangeMap T U q b hq u = p.resultant q m n • u := by
  obtain ⟨a, b, _, _, hab⟩ :=
    exists_mul_add_mul_eq_C_resultant p q hpdeg hqdeg hdegree
  exact ⟨b, polynomialRangeMap_eq_smul T U p q a b _ hp hq hab⟩

end Langlands.Plancherel.PolynomialIsolation
