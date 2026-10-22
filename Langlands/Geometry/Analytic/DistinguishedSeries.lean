import Langlands.Geometry.Analytic.WeierstrassDivision
import Langlands.Geometry.Analytic.TateGaussPoint

/-! # Normalized distinguished series in the actual Tate algebra -/

noncomputable section

universe u

namespace Langlands.Analytic.RestrictedSeries

open Polynomial

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]

theorem normalizedDistinguished_tail_norm_lt_one
    (f : Algebra A) (d : ℕ) (hf : IsNormalizedDistinguished f d) :
    ‖f - ofPolynomial A (trunc A (d + 1) f)‖ < 1 := by
  obtain ⟨i, hi⟩ := StrictTateAlgebra.exists_norm_coeff_eq
    (f - ofPolynomial A (trunc A (d + 1) f))
  rw [← hi]
  rw [← PowerSeries.coeff_def (s := i) rfl]
  change ‖coeff A (i ()) (f - ofPolynomial A (trunc A (d + 1) f))‖ < 1
  rw [map_sub, coeff_ofPolynomial, coeff_trunc]
  split_ifs with hn
  · simp
  · rw [sub_zero]
    exact hf.2.2 (i ()) (by omega)

variable [Nontrivial A]

theorem normalizedDistinguished_trunc_natDegree
    (f : Algebra A) (d : ℕ) (hf : IsNormalizedDistinguished f d) :
    (trunc A (d + 1) f).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_trunc, ite_eq_right (by omega)]
  · rw [coeff_trunc, ite_eq_left (Nat.lt_succ_self d), hf.1]
    exact one_ne_zero

theorem normalizedDistinguished_trunc_monic
    (f : Algebra A) (d : ℕ) (hf : IsNormalizedDistinguished f d) :
    (trunc A (d + 1) f).Monic := by
  change (trunc A (d + 1) f).coeff (trunc A (d + 1) f).natDegree = 1
  rw [normalizedDistinguished_trunc_natDegree f d hf,
    coeff_trunc, ite_eq_left (Nat.lt_succ_self d)]
  exact hf.1

omit [Nontrivial A] in
theorem normalizedDistinguished_trunc_coeff_le
    (f : Algebra A) (d : ℕ) (hf : IsNormalizedDistinguished f d) :
    ∀ n, ‖(trunc A (d + 1) f).coeff n‖ ≤ 1 := by
  intro n
  rw [coeff_trunc]
  split_ifs
  · exact hf.2.1 n
  · simp

variable [CompleteSpace A]

/-- Division by a normalized distinguished series is constructed from its
actual polynomial truncation and strictly small tail. -/
theorem existsUnique_normalizedDistinguished_division
    (f : Algebra A) (d : ℕ) (hf : IsNormalizedDistinguished f d)
    (g : Algebra A) :
    ∃! qr : Algebra A × Polynomial A,
      g = f * qr.1 + ofPolynomial A qr.2 ∧
      qr.2.degree < d ∧ ‖qr.1‖ ≤ ‖g‖ ∧ ‖ofPolynomial A qr.2‖ ≤ ‖g‖ := by
  let p := trunc A (d + 1) f
  have hp : p.Monic := normalizedDistinguished_trunc_monic f d hf
  have heq : ofPolynomial A p + (f - ofPolynomial A p) = f := by abel
  have hd : p.degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero,
      normalizedDistinguished_trunc_natDegree f d hf]
  have h := existsUnique_perturbed_monic_division p hp
    (normalizedDistinguished_trunc_coeff_le f d hf)
    (f - ofPolynomial A p) (normalizedDistinguished_tail_norm_lt_one f d hf) g
  simpa only [heq, hd] using h

end Langlands.Analytic.RestrictedSeries
