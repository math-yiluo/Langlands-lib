import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Nakayama

/-! # Krull dimension bounded by generators of a primary ideal modulo a power -/

namespace Langlands.RingTheory.LocalGeneratorsKrullDimension

variable {O : Type*} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]

/-- Nakayama: if `𝔪 ^ c` lies in the span of `b` up to `𝔪 ^ (c + 1)`, it lies in the span. -/
lemma maximalIdeal_pow_le_span {ι : Type*} (b : ι → O) (c : ℕ)
    (h : IsLocalRing.maximalIdeal O ^ c ≤
      Ideal.span (Set.range b) ⊔ IsLocalRing.maximalIdeal O ^ (c + 1)) :
    IsLocalRing.maximalIdeal O ^ c ≤ Ideal.span (Set.range b) := by
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
    (IsNoetherian.noetherian _) ?_ ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  · rw [Ideal.smul_eq_mul, ← pow_succ']
    exact h

/-- If finitely many elements `b i` of the maximal ideal of a Noetherian local ring span the
`c`-th power of the maximal ideal modulo its `(c + 1)`-st power, then the Krull dimension is at
most the number of elements. -/
theorem ringKrullDim_le_card {ι : Type*} [Fintype ι] (b : ι → O)
    (hb : ∀ i, b i ∈ IsLocalRing.maximalIdeal O) (c : ℕ)
    (h : IsLocalRing.maximalIdeal O ^ c ≤
      Ideal.span (Set.range b) ⊔ IsLocalRing.maximalIdeal O ^ (c + 1)) :
    ringKrullDim O ≤ Fintype.card ι := by
  classical
  have hle := maximalIdeal_pow_le_span b c h
  have hs : ((Finset.univ.image b : Finset O) : Set O) = Set.range b := by simp
  have hmin : IsLocalRing.maximalIdeal O ∈
      (Ideal.span ((Finset.univ.image b : Finset O) : Set O)).minimalPrimes := by
    rw [hs]
    refine ⟨⟨inferInstance, Ideal.span_le.mpr (Set.range_subset_iff.mpr hb)⟩, ?_⟩
    intro q hq _
    exact hq.1.le_of_pow_le (hle.trans hq.2)
  have h₁ := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h₂ : ((Finset.univ.image b).card : ℕ∞) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_image_le.trans (by simp)
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast h₁.trans h₂

end Langlands.RingTheory.LocalGeneratorsKrullDimension
