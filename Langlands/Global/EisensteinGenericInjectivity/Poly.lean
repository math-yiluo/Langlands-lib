import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Complex.Basic

/-! # Energies along monomial curves are polynomial -/

noncomputable section

open Polynomial

namespace Langlands.Global.EisensteinGenericInjectivity

variable {n N : ℕ}

/-- The polynomial expanding a quadratic energy along `t ↦ ∑ t ^ d r • y r`. -/
def energyPoly (B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ) (y : Fin n → Fin N → ℂ) (d : Fin n → ℕ) :
    ℝ[X] :=
  ∑ r, ∑ s, C (B (y r) (y s)) * X ^ (d r + d s)

variable {Q : (Fin N → ℂ) → ℝ} {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ} {y : Fin n → Fin N → ℂ}

theorem eval_energyPoly
    (hexp : ∀ a : Fin n → ℝ, Q (∑ r, (a r : ℂ) • y r) = ∑ r, ∑ s, a r * a s * B (y r) (y s))
    (d : Fin n → ℕ) (t : ℝ) :
    (energyPoly B y d).eval t = Q (∑ r, ((t ^ d r : ℝ) : ℂ) • y r) := by
  rw [hexp]
  simp only [energyPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, pow_add]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

theorem natDegree_energyPoly_le {d : Fin n → ℕ} {D : ℕ} (hd : ∀ r, d r ≤ D) :
    (energyPoly B y d).natDegree ≤ 2 * D := by
  refine natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by have := hd r; have := hd s; omega)

theorem coeff_energyPoly_top
    (hexp : ∀ a : Fin n → ℝ, Q (∑ r, (a r : ℂ) • y r) = ∑ r, ∑ s, a r * a s * B (y r) (y s))
    {d : Fin n → ℕ} {D : ℕ} (hd : ∀ r, d r ≤ D) :
    (energyPoly B y d).coeff (2 * D) =
      Q (∑ r, (((if d r = D then 1 else 0 : ℝ)) : ℂ) • y r) := by
  rw [hexp]
  simp only [energyPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  have hr := hd r
  have hs := hd s
  by_cases hrD : d r = D <;> by_cases hsD : d s = D
  · simp [hrD, hsD, two_mul]
  · have : 2 * D ≠ d r + d s := by omega
    rw [ite_eq_right_iff.mpr fun h => absurd h this]
    simp [hsD]
  · have : 2 * D ≠ d r + d s := by omega
    rw [ite_eq_right_iff.mpr fun h => absurd h this]
    simp [hrD]
  · have : 2 * D ≠ d r + d s := by omega
    rw [ite_eq_right_iff.mpr fun h => absurd h this]
    simp [hrD]

/-- Top coefficients of a finite product of powers of polynomials with degree bounds. -/
theorem coeff_prod_pow_of_natDegree_le {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    (m D : ι → ℕ) (hp : ∀ i ∈ s, (p i).natDegree ≤ D i) :
    (∏ i ∈ s, p i ^ m i).natDegree ≤ ∑ i ∈ s, m i * D i ∧
      (∏ i ∈ s, p i ^ m i).coeff (∑ i ∈ s, m i * D i) = ∏ i ∈ s, (p i).coeff (D i) ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' := ih fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hpa := hp a (Finset.mem_insert_self a s)
    have hpow : (p a ^ m a).natDegree ≤ m a * D a :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ hpa)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨natDegree_mul_le.trans (Nat.add_le_add hpow ih'.1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hpow ih'.1, coeff_pow_of_natDegree_le hpa, ih'.2]

/-- A polynomial with a nonzero coefficient at a positive degree bound takes each value only
finitely often. -/
theorem finite_setOf_eval_eq {p : ℝ[X]} {k : ℕ} (hk : 0 < k)
    (hc : p.coeff k ≠ 0) (c : ℝ) : {t : ℝ | p.eval t = c}.Finite := by
  have hne : p - C c ≠ 0 := by
    intro h
    have h' := congrArg (fun q : ℝ[X] => q.coeff k) h
    simp only [coeff_sub, coeff_C, hk.ne', ite_false, sub_zero, coeff_zero] at h'
    exact hc h'
  refine (finite_setOfPred_isRoot hne).subset fun t ht => ?_
  simp only [Set.mem_ofPred_eq] at ht ⊢
  simp [IsRoot, ht]

end Langlands.Global.EisensteinGenericInjectivity
