import Langlands.MathlibBase
import Langlands.AlgebraicGeometry.PointTopology.HenselianRootLifting

/-!
# Simple roots of arbitrary polynomials over henselian local rings

Mathlib's `HenselianLocalRing` lifts simple residual roots of monic polynomials. This module
removes the monicity: over a henselian local ring every polynomial `f` with `f(a₀) ∈ 𝔪` and
`f'(a₀)` a unit has a root `a ≡ a₀ (mod 𝔪)`, and such a root is unique in any local ring. It also
records that the power series ring over a field is a henselian local ring.
-/

noncomputable section

open Polynomial IsLocalRing

namespace Langlands.CommutativeAlgebra

/-- The power series ring over a field is a henselian local ring: it is complete for its maximal
ideal `(X)`. -/
instance powerSeries_henselianLocalRing (k : Type*) [Field k] :
    HenselianLocalRing (PowerSeries k) where
  is_henselian f hf a₀ h₁ h₂ := by
    rw [PowerSeries.maximalIdeal_eq_span_X] at h₁ ⊢
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

/-- **Simple roots of arbitrary polynomials lift over a henselian local ring.** If `f(a₀)` lies
in the maximal ideal and `f'(a₀)` is a unit, then `f` has a root congruent to `a₀`; `f` need not
be monic. -/
theorem exists_isRoot_sub_mem_maximalIdeal {O : Type*} [CommRing O] [HenselianLocalRing O]
    (f : O[X]) (a₀ : O) (h₁ : f.eval a₀ ∈ maximalIdeal O) (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : O, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal O := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, g = taylor a₀ f := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c, c = f.eval a₀ := ⟨_, rfl⟩
  rw [← hc₀] at h₁
  obtain ⟨u, hu⟩ := h₂
  obtain ⟨n, hn⟩ : ∃ n, n = g.natDegree := ⟨_, rfl⟩
  have hg0 : g.coeff 0 = c₀ := by rw [hg, taylor_coeff_zero, hc₀]
  have hg1 : g.coeff 1 = (u : O) := by rw [hg, taylor_coeff_one, hu]
  have hn1 : 1 ≤ n := hn ▸ le_natDegree_of_ne_zero (by rw [hg1]; exact u.ne_zero)
  -- the rescaled coefficients of `g (-c₀ u⁻¹ W) / c₀`
  let r : ℕ → O := fun i => if i = 0 then 1 else
    g.coeff i * (-(u⁻¹ : Oˣ) : O) ^ i * c₀ ^ (i - 1)
  let P : O[X] := ∑ i ∈ Finset.range (n + 1), C (r i) * X ^ i
  have hPcoeff (i : ℕ) : P.coeff i = if i ≤ n then r i else 0 := by
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range,
      Nat.lt_succ_iff]
  have hP0 : P.coeff 0 = 1 := by rw [hPcoeff]; simp [r]
  have hP1 : P.coeff 1 = -1 := by
    simp only [hPcoeff, hn1, r, one_ne_zero, ite_true, ite_false, pow_one, Nat.sub_self,
      pow_zero, mul_one, hg1]
    simp
  have hPk (i : ℕ) (hi : 2 ≤ i) : P.coeff i ∈ maximalIdeal O := by
    rw [hPcoeff]
    split_ifs
    · have hi0 : i ≠ 0 := by omega
      simp only [r, hi0, ite_false]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h₁ _ (by omega))
    · exact Ideal.zero_mem _
  obtain ⟨W, hW⟩ :=
    Langlands.AlgebraicGeometry.PointTopology.HenselianRoot.exists_isRoot_of_coeff P hP0 hP1 hPk
  obtain ⟨z, hz⟩ : ∃ z, z = -(c₀ * (u⁻¹ : Oˣ) * W) := ⟨_, rfl⟩
  -- `g z = c₀ P(W)`
  have hgz : g.eval z = c₀ * P.eval W := by
    rw [eval_eq_sum_range, ← hn, eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [r, hg0]
    · have hi0 : i ≠ 0 := hi.ne'
      simp only [r, hi0, ite_false, hz]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
  refine ⟨a₀ + z, ?_, ?_⟩
  · have := taylor_eval a₀ f z
    rw [← hg] at this
    show f.eval (a₀ + z) = 0
    rw [add_comm, ← this, hgz, hW.eq_zero, mul_zero]
  · rw [add_sub_cancel_left, hz]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h₁))

/-- **Simple roots are unique in a local ring.** Two roots of `f` congruent modulo the maximal
ideal coincide when `f'` is a unit at one of them. -/
theorem eq_of_isRoot_of_sub_mem_maximalIdeal {O : Type*} [CommRing O] [IsLocalRing O]
    {f : O[X]} {a b : O} (ha : f.IsRoot a) (hb : f.IsRoot b) (hab : a - b ∈ maximalIdeal O)
    (h' : IsUnit (f.derivative.eval a)) : a = b :=
  IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha hb ((mem_maximalIdeal _).1 hab) h'

end Langlands.CommutativeAlgebra
