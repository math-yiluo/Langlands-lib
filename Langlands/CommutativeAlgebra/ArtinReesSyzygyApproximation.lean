import Langlands.CommutativeAlgebra.FinitePiIdealMultiples
import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.LinearCombination

/-! # Approximate generators with approximate syzygies: Artin–Rees comparison -/

universe u v w t

namespace Langlands.CommutativeAlgebra.ArtinReesSyzygyApproximation

open Submodule

variable {Q : Type u} [CommRing Q]

/-- Artin–Rees for the span of a finite family: an element of the span lying in
`I ^ n • M` is a combination of the family with coefficients in `I ^ (n - c)`. -/
theorem exists_artinRees_span [IsNoetherianRing Q] {M : Type t} [AddCommGroup M]
    [Module Q M] [Module.Finite Q M] (I : Ideal Q) {ι : Type v} [Fintype ι] (v : ι → M) :
    ∃ c : ℕ, ∀ n ≥ c, ∀ x ∈ span Q (Set.range v), x ∈ I ^ n • (⊤ : Submodule Q M) →
      ∃ w : ι → Q, (∀ l, w l ∈ I ^ (n - c)) ∧ x = ∑ l, w l • v l := by
  classical
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (span Q (Set.range v))
  refine ⟨c, fun n hn x hx hxn => ?_⟩
  have h1 : x ∈ I ^ (n - c) • span Q (Set.range v) := by
    have : x ∈ I ^ n • (⊤ : Submodule Q M) ⊓ span Q (Set.range v) := ⟨hxn, hx⟩
    rw [hc n hn] at this
    exact Submodule.smul_mono le_rfl inf_le_right this
  obtain ⟨a, ha, rfl⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).mp h1
  exact ⟨fun l => a l, ha, by rw [Finsupp.sum_fintype _ _ (by simp)]⟩

variable (𝔫 : Ideal Q) {ι : Type v} [Fintype ι] {κ : Type w} [Fintype κ]

/-- One improvement step: a representation of `z ∈ 𝔫 ^ d` in the approximate
generators with coefficients in `𝔫 ^ m`, `m + N ≤ d`, can be replaced by one with
coefficients in `𝔫 ^ (m + 1)`. -/
theorem exists_improved_coefficients {c₁ c₂ N : ℕ}
    (b b' : ι → Q) (K K' : κ → ι → Q)
    (hAR₁ : ∀ n ≥ c₁, ∀ x ∈ Ideal.span (Set.range b), x ∈ 𝔫 ^ n →
      ∃ w : ι → Q, (∀ j, w j ∈ 𝔫 ^ (n - c₁)) ∧ x = ∑ j, w j * b j)
    (hAR₂ : ∀ n ≥ c₂, ∀ x ∈ span Q (Set.range K), x ∈ 𝔫 ^ n • (⊤ : Submodule Q (ι → Q)) →
      ∃ w : κ → Q, (∀ l, w l ∈ 𝔫 ^ (n - c₂)) ∧ x = ∑ l, w l • K l)
    (hK : ∀ u : ι → Q, ∑ j, u j * b j = 0 → u ∈ span Q (Set.range K))
    (hK' : ∀ l, ∑ j, K' l j * b' j = 0)
    (hN₁ : c₁ + 1 ≤ N) (hN₂ : c₂ + 1 ≤ N)
    (hb : ∀ j, b' j - b j ∈ 𝔫 ^ N) (hKK : ∀ l j, K' l j - K l j ∈ 𝔫 ^ N)
    {m d : ℕ} (hmd : m + N ≤ d) {z : Q} (hz : z ∈ 𝔫 ^ d)
    (u : ι → Q) (hu : ∀ j, u j ∈ 𝔫 ^ m) (hzu : z = ∑ j, u j * b' j) :
    ∃ u' : ι → Q, (∀ j, u' j ∈ 𝔫 ^ (m + 1)) ∧ z = ∑ j, u' j * b' j := by
  classical
  -- the error of the exact generators
  have herr : ∑ j, u j * (b' j - b j) ∈ 𝔫 ^ (m + N) :=
    Ideal.sum_mem _ fun j _ => by
      rw [pow_add]; exact Ideal.mul_mem_mul (hu j) (hb j)
  set y := ∑ j, u j * b j with hy
  have hy' : y = z - ∑ j, u j * (b' j - b j) := by
    rw [hzu, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hyN : y ∈ 𝔫 ^ (m + N) := by
    rw [hy']
    exact Ideal.sub_mem _ (Ideal.pow_le_pow_right hmd hz) herr
  have hyspan : y ∈ Ideal.span (Set.range b) :=
    Ideal.mem_span_range_iff_exists_fun.mpr ⟨u, rfl⟩
  obtain ⟨v, hv, hyv⟩ := hAR₁ (m + N) (by omega) y hyspan hyN
  -- `u - v` is a syzygy of the exact generators
  have hker : ∑ j, (u - v) j * b j = 0 := by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [← hy, ← hyv, sub_self]
  have hspan := hK (u - v) hker
  have hvm : ∀ j, v j ∈ 𝔫 ^ m := fun j =>
    Ideal.pow_le_pow_right (by omega) (hv j)
  have huvm : (u - v) ∈ 𝔫 ^ m • (⊤ : Submodule Q (ι → Q)) :=
    (mem_ideal_smul_top_pi_iff _ _).mpr fun j => Ideal.sub_mem _ (hu j) (hvm j)
  obtain ⟨w, hw, huvw⟩ : ∃ w : κ → Q, (∀ l, w l ∈ 𝔫 ^ (m - c₂)) ∧
      u - v = ∑ l, w l • K l := by
    by_cases hm : c₂ ≤ m
    · exact hAR₂ m hm _ hspan huvm
    · obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun Q).mp hspan
      refine ⟨w, fun l => ?_, hw.symm⟩
      simp [show m - c₂ = 0 by omega]
  refine ⟨u - ∑ l, w l • K' l, fun j => ?_, ?_⟩
  · -- `u - Σ w K' = v - Σ w (K' - K)`
    have hval : (u - ∑ l, w l • K' l) j = v j - ∑ l, w l * (K' l j - K l j) := by
      have := congrFun huvw j
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      simp only [mul_sub, Finset.sum_sub_distrib]
      linear_combination this
    rw [hval]
    refine Ideal.sub_mem _ (Ideal.pow_le_pow_right (by omega) (hv j))
      (Ideal.sum_mem _ fun l _ => ?_)
    have : w l * (K' l j - K l j) ∈ 𝔫 ^ (m - c₂ + N) := by
      rw [pow_add]; exact Ideal.mul_mem_mul (hw l) (hKK l j)
    exact Ideal.pow_le_pow_right (by omega) this
  · rw [hzu]
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib]
    have : ∑ j, (∑ l, w l * K' l j) * b' j = 0 := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun l _ => by
        simp only [mul_assoc, ← Finset.mul_sum, hK' l, mul_zero]
    rw [this, sub_zero]

/-- **Artin–Rees comparison.** Let `b` generate an ideal of a Noetherian ring and
let the rows of `K` generate the syzygies of `b`. There is `c` such that for all
`N ≥ c + 1` and all `b'`, `K'` congruent to `b`, `K` modulo `𝔫 ^ N` with the rows of
`K'` syzygies of `b'`, every element of `(b') ∩ 𝔫 ^ d` lies in `(b) + 𝔫 ^ (d + 1)`. -/
theorem exists_approximation_order [IsNoetherianRing Q]
    (b : ι → Q) (K : κ → ι → Q)
    (hK : ∀ u : ι → Q, ∑ j, u j * b j = 0 → u ∈ span Q (Set.range K)) :
    ∃ c : ℕ, ∀ N ≥ c + 1, ∀ (b' : ι → Q) (K' : κ → ι → Q),
      (∀ l, ∑ j, K' l j * b' j = 0) →
      (∀ j, b' j - b j ∈ 𝔫 ^ N) → (∀ l j, K' l j - K l j ∈ 𝔫 ^ N) →
      ∀ d : ℕ, ∀ z ∈ Ideal.span (Set.range b'), z ∈ 𝔫 ^ d →
        z ∈ Ideal.span (Set.range b) ⊔ 𝔫 ^ (d + 1) := by
  classical
  obtain ⟨c₁, hc₁⟩ := exists_artinRees_span (M := Q) 𝔫 b
  obtain ⟨c₂, hc₂⟩ := exists_artinRees_span (M := ι → Q) 𝔫 K
  have hAR₁ : ∀ n ≥ c₁, ∀ x ∈ Ideal.span (Set.range b), x ∈ 𝔫 ^ n →
      ∃ w : ι → Q, (∀ j, w j ∈ 𝔫 ^ (n - c₁)) ∧ x = ∑ j, w j * b j := by
    intro n hn x hx hxn
    have hxn' : x ∈ 𝔫 ^ n • (⊤ : Submodule Q Q) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hxn
    obtain ⟨w, hw, hxw⟩ := hc₁ n hn x hx hxn'
    exact ⟨w, hw, by simpa only [smul_eq_mul] using hxw⟩
  refine ⟨max c₁ c₂, fun N hN b' K' hK' hb hKK d z hz hzd => ?_⟩
  have hN₁ : c₁ + 1 ≤ N := le_trans (by omega) hN
  have hN₂ : c₂ + 1 ≤ N := le_trans (by omega) hN
  -- by induction, either done or a representation with coefficients in `𝔫 ^ m`
  have key : ∀ m : ℕ, z ∈ Ideal.span (Set.range b) ⊔ 𝔫 ^ (d + 1) ∨
      ∃ u : ι → Q, (∀ j, u j ∈ 𝔫 ^ m) ∧ z = ∑ j, u j * b' j := by
    intro m
    induction m with
    | zero =>
      obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hz
      exact Or.inr ⟨u, fun j => by simp, hu.symm⟩
    | succ m ih =>
      rcases ih with h | ⟨u, hu, hzu⟩
      · exact Or.inl h
      by_cases hmd : m + N ≤ d
      · exact Or.inr (exists_improved_coefficients 𝔫 b b' K K' hAR₁ hc₂ hK hK' hN₁ hN₂
          hb hKK hmd hzd u hu hzu)
      · left
        have hsplit : z = ∑ j, u j * b j + ∑ j, u j * (b' j - b j) := by
          rw [hzu, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hsplit]
        refine Submodule.add_mem_sup
          (Ideal.mem_span_range_iff_exists_fun.mpr ⟨u, rfl⟩) ?_
        refine Ideal.pow_le_pow_right (show d + 1 ≤ m + N by omega) ?_
        exact Ideal.sum_mem _ fun j _ => by
          rw [pow_add]; exact Ideal.mul_mem_mul (hu j) (hb j)
  rcases key (d + 1) with h | ⟨u, hu, hzu⟩
  · exact h
  · refine Ideal.mem_sup_right ?_
    rw [hzu]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hu j)

end Langlands.CommutativeAlgebra.ArtinReesSyzygyApproximation
