import Langlands.Analysis.Local.FiniteCoverCharacterStatement
import Mathlib.GroupTheory.OrderOfElement

noncomputable section

universe u

open scoped NNReal

namespace Langlands.Haar

/-- The finite exceptional factor contains every character value. -/
theorem character_range_finite_of_product_cover {G : Type u} [Group G]
    (χ : G →* ℝ≥0) (K : Subgroup G) (A E : Set G) (hE : E.Finite)
    (hK : ∀ k ∈ K, χ k = 1) (hA : ∀ a ∈ A, χ a = 1)
    (hcover : ∀ g : G, ∃ k₁ ∈ K, ∃ a ∈ A, ∃ e ∈ E, ∃ k₂ ∈ K,
      g = k₁ * a * e * k₂) :
    (Set.range χ).Finite := by
  apply (hE.image χ).subset
  rintro _ ⟨g, rfl⟩
  obtain ⟨k₁, hk₁, a, ha, e, he, k₂, hk₂, rfl⟩ := hcover g
  refine ⟨e, he, ?_⟩
  simp [map_mul, hK k₁ hk₁, hK k₂ hk₂, hA a ha]

/-- A finite product cover gives triviality of a positive character. -/
theorem finiteCoverCharacter : FiniteCoverCharacterStatement.{u} := by
  intro G _ χ K A E hE hK hA hcover g
  have hχ := character_range_finite_of_product_cover χ K A E hE hK hA hcover
  let φ := χ.toHomUnits
  have hφ : (Set.range φ).Finite := by
    apply (hχ.preimage Units.val_injective.injOn).subset
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have : Finite φ.range := hφ.to_subtype
  obtain ⟨n, hn, hpow⟩ :=
    (isOfFinOrder_of_finite (φ.rangeRestrict g)).exists_pow_eq_one
  have hval : χ g ^ n = 1 := by
    simpa [φ] using
      congrArg (fun z : φ.range => ((z : ℝ≥0ˣ) : ℝ≥0)) hpow
  exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp hval

end Langlands.Haar
