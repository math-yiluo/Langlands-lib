import Langlands.Analysis.FiniteNatLatticeSummabilityStatement
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option

/-! # Polynomial-geometric summability on finite natural-number lattices -/

namespace Langlands

open scoped BigOperators ENNReal

universe uI

/-- A shifted natural power times a geometric sequence is summable. -/
theorem summable_one_add_nat_pow_mul_geometric (d : ℕ) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ d * r ^ n) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr₀] using hr₁
  have h := summable_sum (s := Finset.range (d + 1))
    (fun j _ => (summable_pow_mul_geometric_of_norm_lt_one j hr).mul_right
      (d.choose j : ℝ))
  convert h using 1
  ext n
  rw [add_comm (1 : ℝ), add_pow, Finset.sum_mul]
  simp only [one_pow, mul_one]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Products of nonnegative summable coordinate functions are summable on a
finite natural-number tuple space. The empty tuple space is included. -/
theorem summable_fintype_nat_prod (I : Type*) [Fintype I] :
    ∀ (f : I → ℕ → ℝ), (∀ i n, 0 ≤ f i n) →
      (∀ i, Summable (f i)) →
      Summable (fun k : I → ℕ => ∏ i, f i (k i)) := by
  classical
  apply Fintype.induction_empty_option
    (P := fun I _ => ∀ (f : I → ℕ → ℝ), (∀ i n, 0 ≤ f i n) →
      (∀ i, Summable (f i)) →
      Summable (fun k : I → ℕ => ∏ i, f i (k i)))
  · intro A B _ e ih f hf hs
    let : Fintype A := Fintype.ofEquiv B e.symm
    let eK : (B → ℕ) ≃ (A → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have h := eK.summable_iff.mpr
      (ih (fun i => f (e i)) (fun i => hf (e i)) (fun i => hs (e i)))
    convert h using 1
    ext k
    exact (e.prod_comp (fun i => f i (k i))).symm
  · intro f _ _
    exact (hasSum_fintype _).summable
  · intro A _ ih f hf hs
    have h := (hs none).mul_of_nonneg
      (ih (fun i => f (some i)) (fun i => hf (some i)) (fun i => hs (some i)))
      (hf none) (fun k => Finset.prod_nonneg (fun i _ => hf (some i) (k i)))
    have h' := (Equiv.piOptionEquivProd (β := fun _ : Option A => ℕ)).summable_iff.mpr h
    simpa only [Function.comp_def, Equiv.piOptionEquivProd_apply, Fintype.prod_option] using h'

/-- A nonnegative finite sum plus one is bounded by the product of the
coordinate increments. -/
theorem one_add_sum_le_prod_one_add {I : Type*} (t : Finset I) (a : I → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) :
    1 + ∑ i ∈ t, a i ≤ ∏ i ∈ t, (1 + a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      have hi₀ := ha i (Finset.mem_insert_self _ _)
      have ht₀ : ∀ j ∈ t, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hs₀ : 0 ≤ ∑ j ∈ t, a j := Finset.sum_nonneg ht₀
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        1 + (a i + ∑ j ∈ t, a j) ≤ (1 + a i) * (1 + ∑ j ∈ t, a j) := by
          nlinarith [mul_nonneg hi₀ hs₀]
        _ ≤ (1 + a i) * ∏ j ∈ t, (1 + a j) :=
          mul_le_mul_of_nonneg_left (ih ht₀) (by positivity)

/-- Real polynomial-geometric summability on every finite natural-number
lattice. -/
theorem finiteNatLatticeRealSummability :
    FiniteNatLatticeRealSummabilityStatement.{uI} := by
  intro I _ r hr₀ hr₁ s _hs
  obtain ⟨d, hd⟩ := exists_nat_ge s
  have hbound := summable_fintype_nat_prod I
    (fun i n => (1 + (n : ℝ)) ^ d * r i ^ n)
    (fun i n => mul_nonneg (by positivity) (pow_nonneg (hr₀ i) n))
    (fun i => summable_one_add_nat_pow_mul_geometric d (hr₀ i) (hr₁ i))
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Real.rpow_nonneg
      (add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (k i)))) s)
      (Finset.prod_nonneg (fun i _ => pow_nonneg (hr₀ i) (k i)))) _ hbound
  intro k
  have hh : 1 ≤ 1 + ∑ i, (k i : ℝ) := by
    have : 0 ≤ ∑ i, (k i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
    linarith
  have hp := one_add_sum_le_prod_one_add Finset.univ (fun i => (k i : ℝ))
    (fun i _ => Nat.cast_nonneg _)
  have hrpow : Real.rpow (1 + ∑ i, (k i : ℝ)) s ≤
      (∏ i, (1 + (k i : ℝ))) ^ d := by
    calc
      Real.rpow (1 + ∑ i, (k i : ℝ)) s ≤
          Real.rpow (1 + ∑ i, (k i : ℝ)) (d : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hh hd
      _ = (1 + ∑ i, (k i : ℝ)) ^ d := Real.rpow_natCast _ _
      _ ≤ (∏ i, (1 + (k i : ℝ))) ^ d :=
        pow_le_pow_left₀ (le_trans zero_le_one hh) hp d
  calc
    Real.rpow (1 + ∑ i, (k i : ℝ)) s * ∏ i, r i ^ k i ≤
        (∏ i, (1 + (k i : ℝ))) ^ d * ∏ i, r i ^ k i :=
      mul_le_mul_of_nonneg_right hrpow
        (Finset.prod_nonneg (fun i _ => pow_nonneg (hr₀ i) (k i)))
    _ = ∏ i, ((1 + (k i : ℝ)) ^ d * r i ^ k i) := by
      rw [← Finset.prod_pow, Finset.prod_mul_distrib]

/-- ENNReal finiteness of exactly the same polynomial-geometric summand. -/
theorem finiteNatLatticeENNRealSummability :
    FiniteNatLatticeENNRealSummabilityStatement.{uI} := by
  intro I _ r hr₀ hr₁ s hs
  exact (finiteNatLatticeRealSummability I r hr₀ hr₁ s hs).tsum_ofReal_lt_top

/-- Polynomial-geometric summability, in both the real and ENNReal forms. -/
theorem finiteNatLatticeSummability : FiniteNatLatticeSummabilityStatement.{uI} :=
  ⟨finiteNatLatticeRealSummability, finiteNatLatticeENNRealSummability⟩

end Langlands
