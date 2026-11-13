import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

/-! # Quotients compared through endomorphisms congruent to the identity -/

universe u v

namespace Langlands.CommutativeAlgebra.NearIdentityQuotientComparison

variable {Q : Type u} [CommRing Q] (𝔫 : Ideal Q)

/-- An endomorphism congruent to the identity modulo `𝔫 ^ 2` moves every element of
`𝔫 ^ k` by an element of `𝔫 ^ (k + 1)`. -/
theorem sub_mem_pow_succ_of_forall_sub_mem_sq (Φ : Q →+* Q)
    (hΦ : ∀ x, Φ x - x ∈ 𝔫 ^ 2) : ∀ k : ℕ, ∀ x ∈ 𝔫 ^ k, Φ x - x ∈ 𝔫 ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro x _; simpa using Ideal.pow_le_pow_right (show 1 ≤ 2 by omega) (hΦ x)
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      have hΦa : Φ a ∈ 𝔫 ^ k := by
        have := Ideal.add_mem _ ha (Ideal.pow_le_pow_right (by omega) (ih a ha))
        simpa using this
      have h1 : Φ a * (Φ b - b) ∈ 𝔫 ^ (k + 1 + 1) := by
        have : Φ a * (Φ b - b) ∈ 𝔫 ^ k * 𝔫 ^ 2 := Ideal.mul_mem_mul hΦa (hΦ b)
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this
      have h2 : (Φ a - a) * b ∈ 𝔫 ^ (k + 1 + 1) := by
        have : (Φ a - a) * b ∈ 𝔫 ^ (k + 1) * 𝔫 := Ideal.mul_mem_mul (ih a ha) hb
        rwa [← pow_succ] at this
      have : Φ (a * b) - a * b = Φ a * (Φ b - b) + (Φ a - a) * b := by
        rw [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ h1 h2
    · intro x y hx hy
      have : Φ (x + y) - (x + y) = (Φ x - x) + (Φ y - y) := by rw [map_add]; ring
      rw [this]
      exact Ideal.add_mem _ hx hy

variable {𝔫} {Φ : Q →+* Q} (hΦ : ∀ k : ℕ, ∀ x ∈ 𝔫 ^ k, Φ x - x ∈ 𝔫 ^ (k + 1))
include hΦ

/-- A near-identity endomorphism is surjective modulo every power of `𝔫`. -/
theorem exists_sub_map_mem_pow (k : ℕ) (y : Q) : ∃ x, y - Φ x ∈ 𝔫 ^ k := by
  induction k generalizing y with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨x, hx⟩ := ih y
    refine ⟨x + (y - Φ x), ?_⟩
    have : y - Φ (x + (y - Φ x)) = -(Φ (y - Φ x) - (y - Φ x)) := by
      rw [map_add]; ring
    rw [this]
    exact neg_mem (hΦ k _ hx)

/-- A near-identity endomorphism reflects membership in every power of `𝔫`. -/
theorem mem_pow_of_map_mem_pow {n : ℕ} {y : Q} (hy : Φ y ∈ 𝔫 ^ n) : y ∈ 𝔫 ^ n := by
  have : ∀ k ≤ n, y ∈ 𝔫 ^ k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hyk := ih (by omega)
      have : y = Φ y - (Φ y - y) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.pow_le_pow_right hk hy) (hΦ k y hyk)
  exact this n le_rfl

/-- **Comparison of quotients.** Let `Φ` be a near-identity endomorphism carrying `I`
into `I' + 𝔫 ^ n`, and assume `I' ∩ 𝔫 ^ d ⊆ I + 𝔫 ^ (d + 1)` for `d < n`. Then `Φ`
carries the ideal `I + 𝔫 ^ n` exactly onto the preimage of `I' + 𝔫 ^ n`. -/
theorem map_mem_sup_iff {I I' : Ideal Q} {n : ℕ} (hI : ∀ x ∈ I, Φ x ∈ I' ⊔ 𝔫 ^ n)
    (hAR : ∀ d < n, I' ⊓ 𝔫 ^ d ≤ I ⊔ 𝔫 ^ (d + 1)) (x : Q) :
    Φ x ∈ I' ⊔ 𝔫 ^ n ↔ x ∈ I ⊔ 𝔫 ^ n := by
  -- every element of `I'` is congruent to the image of an element of `I`
  have key : ∀ d ≤ n, ∀ z ∈ I', ∃ i ∈ I, z - Φ i ∈ (I' ⊔ 𝔫 ^ n) ⊓ 𝔫 ^ d := by
    intro d
    induction d with
    | zero =>
      intro _ z hz
      exact ⟨0, I.zero_mem, by simpa using Ideal.mem_sup_left hz⟩
    | succ d ih =>
      intro hd z hz
      obtain ⟨i, hi, hzi₁, hzi₂⟩ := ih (by omega) z hz
      obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.mp hzi₁
      have hed : e ∈ 𝔫 ^ d := Ideal.pow_le_pow_right (by omega) he
      have had : a ∈ 𝔫 ^ d := by
        have : a = (z - Φ i) - e := by rw [← hae]; ring
        rw [this]; exact Ideal.sub_mem _ hzi₂ hed
      obtain ⟨j, hj, f, hf, hjf⟩ := Submodule.mem_sup.mp (hAR d (by omega) ⟨ha, had⟩)
      have hjd : j ∈ 𝔫 ^ d := by
        have : j = a - f := by rw [← hjf]; ring
        rw [this]
        exact Ideal.sub_mem _ had (Ideal.pow_le_pow_right (by omega) hf)
      refine ⟨i + j, I.add_mem hi hj, ?_, ?_⟩
      · rw [map_add, sub_add_eq_sub_sub]
        exact Ideal.sub_mem _ hzi₁ (hI j hj)
      · have : z - Φ (i + j) = -(Φ j - j) + f + e := by
          rw [map_add]
          linear_combination -hae - hjf
        rw [this]
        refine Ideal.add_mem _ (Ideal.add_mem _ (neg_mem (hΦ d j hjd)) hf)
          (Ideal.pow_le_pow_right (by omega) he)
  constructor
  · intro hx
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.mp hx
    obtain ⟨i, hi, -, hai'⟩ := key n le_rfl a ha
    have hdiff : Φ (x - i) ∈ 𝔫 ^ n := by
      have : Φ (x - i) = (a - Φ i) + e := by rw [map_sub, ← hae]; ring
      rw [this]; exact Ideal.add_mem _ hai' he
    have := mem_pow_of_map_mem_pow hΦ hdiff
    have hx' : x = i + (x - i) := by ring
    rw [hx']
    exact Submodule.add_mem_sup hi this
  · intro hx
    obtain ⟨i, hi, e, he, hie⟩ := Submodule.mem_sup.mp hx
    rw [← hie, map_add]
    refine Ideal.add_mem _ (hI i hi) (Ideal.mem_sup_right ?_)
    have : Φ e = e + (Φ e - e) := by ring
    rw [this]
    exact Ideal.add_mem _ he (Ideal.pow_le_pow_right (by omega) (hΦ n e he))

/-- Packaged form: if `q'` has kernel `I' + 𝔫 ^ n` and `θ = q' ∘ Φ`, then `θ` has kernel
`I + 𝔫 ^ n`, and `θ` is surjective when `q'` is. -/
theorem ker_comp_eq_and_surjective {B : Type v} [CommRing B] {I I' : Ideal Q} {n : ℕ}
    (hI : ∀ x ∈ I, Φ x ∈ I' ⊔ 𝔫 ^ n)
    (hAR : ∀ d < n, I' ⊓ 𝔫 ^ d ≤ I ⊔ 𝔫 ^ (d + 1))
    (q' : Q →+* B) (hq' : RingHom.ker q' = I' ⊔ 𝔫 ^ n) (hsurj : Function.Surjective q') :
    RingHom.ker (q'.comp Φ) = I ⊔ 𝔫 ^ n ∧ Function.Surjective (q'.comp Φ) := by
  refine ⟨?_, ?_⟩
  · ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hq']
    exact map_mem_sup_iff hΦ hI hAR x
  · intro b
    obtain ⟨y, rfl⟩ := hsurj b
    obtain ⟨x, hx⟩ := exists_sub_map_mem_pow hΦ n y
    refine ⟨x, ?_⟩
    have : y - Φ x ∈ RingHom.ker q' := by rw [hq']; exact Ideal.mem_sup_right hx
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this.symm

end Langlands.CommutativeAlgebra.NearIdentityQuotientComparison
