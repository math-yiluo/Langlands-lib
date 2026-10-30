import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Continuous positive characters on compact subgroups -/

open scoped NNReal

namespace Langlands.RankinSelberg.LastRowReduction

/-- A continuous homomorphism to `ℝ≥0ˣ` is trivial on a compact subgroup. -/
theorem eq_one_of_isCompact {G : Type*} [Group G] [TopologicalSpace G]
    (χ : G →* ℝ≥0ˣ) (hχ : Continuous χ) (J : Subgroup G) (hJ : IsCompact (J : Set G))
    {j : G} (hj : j ∈ J) : χ j = 1 := by
  let f : G → ℝ := fun g => ((χ g : ℝ≥0) : ℝ)
  have hf : Continuous f := NNReal.continuous_coe.comp (Units.continuous_val.comp hχ)
  obtain ⟨M, hM⟩ := (hJ.image hf).bddAbove
  have hpow (g : G) (k : ℕ) : f (g ^ k) = f g ^ k := by
    simp [f, map_pow]
  have hbig : ∀ g ∈ J, ¬ 1 < f g := by
    intro g hg hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hlt
    have := hM ⟨g ^ k, J.pow_mem hg k, rfl⟩
    rw [hpow] at this
    exact absurd this (not_le.mpr hk)
  have hpos : 0 < f j := by
    simp only [f, NNReal.coe_pos]
    exact pos_iff_ne_zero.mpr (χ j).ne_zero
  have hinv : f j⁻¹ = (f j)⁻¹ := by
    simp [f, map_inv]
  have h1 : ¬ 1 < f j := hbig j hj
  have h2 : ¬ 1 < f j⁻¹ := hbig j⁻¹ (J.inv_mem hj)
  rw [hinv, one_lt_inv₀ hpos] at h2
  have hfj : f j = 1 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
  apply Units.ext
  apply NNReal.eq
  exact hfj

end Langlands.RankinSelberg.LastRowReduction
