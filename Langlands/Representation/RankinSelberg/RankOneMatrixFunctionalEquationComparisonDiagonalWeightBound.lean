import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Absorbing bounded-diagonal monomial growth into one determinant power. -/

noncomputable section

namespace Langlands.RankinSelberg

open scoped BigOperators

/-- One determinant power for every upper-root denominator and for every
inverse coordinate factor in the slice-volume monomial. -/
def diagonalWeightDegree (n : ℕ) (e : Fin (n + 1) → ℕ) : ℕ :=
  (∑ i : Fin (n + 1), (Finset.univ.filter fun j : Fin (n + 1) => i < j).card) + ∑ i, e i

/-- On a bounded positive diagonal box, the inverse upper-Borel modulus
and every inverse-coordinate monomial are bounded after multiplication by
a fixed nonnegative integral power of the determinant. -/
theorem diagonalWeight_mul_det_pow_le (n : ℕ) (e : Fin (n + 1) → ℕ) (ρ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin (n + 1) → ℝ,
      (∀ i, 0 < x i) → (∀ i, x i ≤ ρ) →
      (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
        x i / x j)⁻¹ * (∏ i, (x i)⁻¹ ^ e i) *
          (∏ i, x i) ^ diagonalWeightDegree n e ≤ C := by
  classical
  let R : ℝ := max 1 ρ
  let A : ℝ := R ^ (n + 1)
  let M : ℕ := ∑ i : Fin (n + 1),
    (Finset.univ.filter fun j : Fin (n + 1) => i < j).card
  let E : ℕ := ∑ i : Fin (n + 1), e i
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hA : 0 ≤ A := pow_nonneg hR0 _
  refine ⟨(R * A) ^ M * A ^ E, mul_nonneg (pow_nonneg (mul_nonneg hR0 hA) _) (pow_nonneg hA _), ?_⟩
  intro x hx hbox
  let D : ℝ := ∏ i, x i
  have hD : 0 < D := Finset.prod_pos fun i _ => hx i
  have hxi (i : Fin (n + 1)) : x i ≤ R := (hbox i).trans (le_max_right _ _)
  have hinv (i : Fin (n + 1)) : (x i)⁻¹ * D ≤ A := by
    have hDeq : D = x i * ∏ j ∈ Finset.univ.erase i, x j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [hDeq, ← mul_assoc, inv_mul_cancel₀ (hx i).ne', one_mul]
    calc
      _ ≤ ∏ j ∈ Finset.univ.erase i, R :=
        Finset.prod_le_prod₀ (fun j _ => (hx j).le) (fun j _ => hxi j)
      _ = R ^ (Finset.univ.erase i).card := Finset.prod_const R
      _ ≤ R ^ (n + 1) := by
        apply pow_le_pow_right₀ hR
        exact (Finset.card_erase_le).trans (by simp)
  have hpair (i j : Fin (n + 1)) : (x i / x j)⁻¹ * D ≤ R * A := by
    calc
      (x i / x j)⁻¹ * D = x j * ((x i)⁻¹ * D) := by rw [inv_div, div_eq_mul_inv]; ring
      _ ≤ R * A := mul_le_mul (hxi j) (hinv i)
        (mul_nonneg (inv_nonneg.mpr (hx i).le) hD.le) hR0
  have hroot : (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter
      (fun j : Fin (n + 1) => i < j), (x i / x j)⁻¹ * D) ≤ (R * A) ^ M := by
    calc
      _ ≤ ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter
          (fun j : Fin (n + 1) => i < j), R * A := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact Finset.prod_nonneg fun j hj =>
            mul_nonneg (inv_nonneg.mpr (div_nonneg (hx i).le (hx j).le)) hD.le
        · intro i hi
          exact Finset.prod_le_prod₀
            (fun j hj => mul_nonneg (inv_nonneg.mpr (div_nonneg (hx i).le (hx j).le)) hD.le)
            (fun j hj => hpair i j)
      _ = (R * A) ^ M := by simp only [Finset.prod_const, Finset.prod_pow_eq_pow_sum, M]
  have hrootId : (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter
      (fun j : Fin (n + 1) => i < j), (x i / x j)⁻¹ * D) =
      (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter
        (fun j : Fin (n + 1) => i < j), x i / x j)⁻¹ * D ^ M := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
      Finset.prod_inv_distrib, M]
  rw [hrootId] at hroot
  have hmono : (∏ i : Fin (n + 1), ((x i)⁻¹ * D) ^ e i) ≤ A ^ E := by
    calc
      _ ≤ ∏ i : Fin (n + 1), A ^ e i := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact pow_nonneg (mul_nonneg (inv_nonneg.mpr (hx i).le) hD.le) _
        · intro i hi
          exact pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr (hx i).le) hD.le) (hinv i) _
      _ = A ^ E := Finset.prod_pow_eq_pow_sum _ _ _
  have hmonoId : (∏ i : Fin (n + 1), ((x i)⁻¹ * D) ^ e i) =
      (∏ i, (x i)⁻¹ ^ e i) * D ^ E := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, E]
  rw [hmonoId] at hmono
  change _ * _ * D ^ (M + E) ≤ _
  rw [pow_add]
  calc
    _ = ((∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter
          (fun j : Fin (n + 1) => i < j), x i / x j)⁻¹ * D ^ M) *
        ((∏ i, (x i)⁻¹ ^ e i) * D ^ E) := by ring
    _ ≤ (R * A) ^ M * A ^ E := mul_le_mul hroot hmono
      (mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hx i).le) _)
        (pow_nonneg hD.le _)) (pow_nonneg (mul_nonneg hR0 hA) _)

end Langlands.RankinSelberg
