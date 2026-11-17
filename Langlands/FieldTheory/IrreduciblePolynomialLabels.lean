import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Set.Card

/-!
# The polynomial set `𝔍(n, k)` of Bushnell–Kutzko

The monic irreducible polynomials of degree `n` over a field `k`, with `X` removed.
Over a finite field this set is finite; in degree `0` it is empty.
-/

namespace Langlands.FieldTheory

open Polynomial

universe u

/-- Bushnell–Kutzko's `𝔍(n, k)`: the monic irreducible polynomials in `k[X]` of degree `n`,
with the polynomial `X` removed (which only changes the set when `n = 1`). -/
def irreduciblePolynomialLabels (n : ℕ) (k : Type u) [Field k] : Set k[X] :=
  {P | P.Monic ∧ Irreducible P ∧ P.natDegree = n} \ {X}

theorem mem_irreduciblePolynomialLabels_iff {n : ℕ} {k : Type u} [Field k] {P : k[X]} :
    P ∈ irreduciblePolynomialLabels n k ↔
      P.Monic ∧ Irreducible P ∧ P.natDegree = n ∧ P ≠ X := by
  simp only [irreduciblePolynomialLabels, Set.mem_sdiff, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, and_assoc]

/-- Away from degree one, removing `X` changes nothing. -/
theorem mem_irreduciblePolynomialLabels_iff_of_ne_one {n : ℕ} (hn : n ≠ 1) {k : Type u}
    [Field k] {P : k[X]} :
    P ∈ irreduciblePolynomialLabels n k ↔ P.Monic ∧ Irreducible P ∧ P.natDegree = n := by
  rw [mem_irreduciblePolynomialLabels_iff]
  constructor
  · exact fun h => ⟨h.1, h.2.1, h.2.2.1⟩
  · rintro ⟨hm, hi, hd⟩
    refine ⟨hm, hi, hd, ?_⟩
    rintro rfl
    exact hn (hd.symm.trans natDegree_X)

/-- In degree `0` the set is empty: the only monic polynomial of degree `0` is `1`, a unit. -/
theorem irreduciblePolynomialLabels_zero (k : Type u) [Field k] :
    irreduciblePolynomialLabels 0 k = ∅ := by
  ext P
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hP
  obtain ⟨hm, hi, hd, -⟩ := mem_irreduciblePolynomialLabels_iff.mp hP
  have h1 : P = 1 := eq_one_of_monic_natDegree_zero hm hd
  subst h1
  exact hi.not_isUnit isUnit_one

/-- Over a finite field there are finitely many polynomials of bounded degree. -/
theorem finite_setOf_natDegree_le (k : Type u) [Field k] [Finite k] (n : ℕ) :
    {P : k[X] | P.natDegree ≤ n}.Finite := by
  refine Set.Finite.of_finite_image (f := fun P : k[X] => fun i : Fin (n + 1) => P.coeff i)
    (Set.toFinite _) ?_
  intro P hP Q hQ h
  ext i
  by_cases hi : i ≤ n
  · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
  · have hlt : n < i := Nat.lt_of_not_le hi
    have hP' : P.natDegree ≤ n := hP
    have hQ' : Q.natDegree ≤ n := hQ
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP' hlt),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ' hlt)]

/-- Over a finite field `𝔍(n, k)` is finite. -/
theorem irreduciblePolynomialLabels_finite (n : ℕ) (k : Type u) [Field k] [Finite k] :
    (irreduciblePolynomialLabels n k).Finite :=
  (finite_setOf_natDegree_le k n).subset fun _ hP =>
    (mem_irreduciblePolynomialLabels_iff.mp hP).2.2.1.le

end Langlands.FieldTheory
