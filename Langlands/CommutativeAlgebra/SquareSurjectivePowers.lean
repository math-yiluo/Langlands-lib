import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps

/-! # Surjectivity modulo the square of an ideal propagates to all powers -/

universe u v

namespace Langlands.CommutativeAlgebra.SquareSurjectivePowers

variable {S : Type u} {A : Type v} [CommRing S] [CommRing A] (φ : S →+* A) (u : Ideal A)

/-- Images of powers of the preimage ideal lie in the powers of the ideal. -/
lemma map_mem_pow {k : ℕ} {s : S} (hs : s ∈ (u.comap φ) ^ k) : φ s ∈ u ^ k := by
  have : φ s ∈ (u.comap φ).map φ ^ k := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ hs
  exact Ideal.pow_right_mono Ideal.map_comap_le k this

/-- If every element is congruent modulo `u ^ 2` to an image, then every element of
`u ^ k` (`k ≥ 1`) is congruent modulo `u ^ (k + 1)` to the image of an element of
`(φ⁻¹ u) ^ k`. -/
theorem exists_mem_pow_sub_mem_pow_succ (h : ∀ a, ∃ s, a - φ s ∈ u ^ 2) :
    ∀ k, 1 ≤ k → ∀ t ∈ u ^ k, ∃ s ∈ (u.comap φ) ^ k, t - φ s ∈ u ^ (k + 1) := by
  have h₁ : ∀ t ∈ u, ∃ s ∈ u.comap φ, t - φ s ∈ u ^ 2 := by
    intro t ht
    obtain ⟨s, hs⟩ := h t
    refine ⟨s, ?_, hs⟩
    change φ s ∈ u
    have : φ s = t - (t - φ s) := by ring
    rw [this]
    exact Ideal.sub_mem _ ht (Ideal.pow_le_self two_ne_zero hs)
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro t ht
    rw [pow_one] at ht
    obtain ⟨s, hs, hts⟩ := h₁ t ht
    exact ⟨s, by rwa [pow_one], hts⟩
  | succ k hk ih =>
    intro t ht
    rw [pow_succ] at ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro a ha b hb
      obtain ⟨s₁, hs₁, e₁⟩ := ih a ha
      obtain ⟨s₂, hs₂, e₂⟩ := h₁ b hb
      refine ⟨s₁ * s₂, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul hs₁ hs₂
      · have hφ₁ : φ s₁ ∈ u ^ k := map_mem_pow φ u hs₁
        have hφ₂ : φ s₂ ∈ u := hs₂
        have : a * b - φ (s₁ * s₂) =
            φ s₁ * (b - φ s₂) + (a - φ s₁) * φ s₂ + (a - φ s₁) * (b - φ s₂) := by
          rw [map_mul]; ring
        rw [this]
        refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
        · have := Ideal.mul_mem_mul hφ₁ e₂
          rw [← pow_add] at this
          exact Ideal.pow_le_pow_right (by omega) this
        · have := Ideal.mul_mem_mul e₁ hφ₂
          rwa [← pow_succ] at this
        · have := Ideal.mul_mem_mul e₁ e₂
          rw [← pow_add] at this
          exact Ideal.pow_le_pow_right (by omega) this
    · rintro x y ⟨s₁, hs₁, e₁⟩ ⟨s₂, hs₂, e₂⟩
      refine ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, ?_⟩
      have : x + y - φ (s₁ + s₂) = (x - φ s₁) + (y - φ s₂) := by rw [map_add]; ring
      rw [this]
      exact Ideal.add_mem _ e₁ e₂

/-- Surjectivity modulo `u ^ 2` implies surjectivity modulo every power of `u`. -/
theorem exists_sub_mem_pow (h : ∀ a, ∃ s, a - φ s ∈ u ^ 2) (k : ℕ) (a : A) :
    ∃ s, a - φ s ∈ u ^ k := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨s, hs⟩ := h a
      exact ⟨s, Ideal.pow_le_pow_right (by omega) hs⟩
    · obtain ⟨s, hs⟩ := ih
      obtain ⟨s', -, hs'⟩ := exists_mem_pow_sub_mem_pow_succ φ u h k hk _ hs
      refine ⟨s + s', ?_⟩
      have : a - φ (s + s') = a - φ s - φ s' := by rw [map_add]; ring
      rwa [this]

end Langlands.CommutativeAlgebra.SquareSurjectivePowers
