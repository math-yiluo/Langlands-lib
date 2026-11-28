import Langlands.BushnellKutzko.SplitTypeRefinement
import Langlands.BushnellKutzko.DiagonalSplitTypeRefinement

/-! # Refinement by a shift followed by a transfer

An abstract form of the induction of Bushnell–Kutzko (8.2.14)–(8.2.28): a shift element `z`
moves a vector outside the relations of `M_j` that is isotypic for `K` to a vector outside the
relations of `M_{j-1}` that is isotypic for `z⁻¹ K z`, and a transfer statement returns to a
vector isotypic for `K`. -/

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

open BushnellKutzko.SplitBlocks in
/-- **Refinement by shift and transfer.** Let `M` be an antitone family of subgroups covering
`U`, and let `P` be the finite-dimensional `ϑ`-isotypic subspace of `K`, not contained in the
relations of `M j₀`. Let `z` satisfy `z M_{j-1} z⁻¹ ⊆ M_j`. If every vector outside the
relations of `M_{j-1}` on which `z⁻¹ k z` acts by `ϑ(k)` for `k ∈ K` gives a vector of `P`
outside these relations, then `P` is not contained in the relations of `U`. -/
theorem not_le_relations_of_shift_transfer (ρ : Representation ℂ G V) (U : Subgroup G)
    (M : ℤ → Subgroup G) (hanti : Antitone M) (hexh : ∀ u ∈ U, ∃ j, u ∈ M j)
    (K : Subgroup G) (ϑ : K →* ℂˣ)
    [FiniteDimensional ℂ (characterSubspace ρ K ϑ)] (j₀ : ℤ)
    (h₀ : ¬ characterSubspace ρ K ϑ ≤ relations ρ (M j₀)) (z : G)
    (hzM : ∀ j, ∀ n ∈ M (j - 1), z * n * z⁻¹ ∈ M j)
    (htransfer : ∀ j (v : V), (∀ k : K, ρ (z⁻¹ * k * z) v = (ϑ k : ℂ) • v) →
      v ∉ relations ρ (M (j - 1)) →
      ∃ w ∈ characterSubspace ρ K ϑ, w ∉ relations ρ (M (j - 1))) :
    ¬ characterSubspace ρ K ϑ ≤ relations ρ U := by
  refine not_le_relations_of_refinement ρ U M hanti hexh _ j₀ h₀ ?_
  intro j hj
  obtain ⟨v₁, hv₁P, hv₁M⟩ := Set.not_subset.mp hj
  have hv₁ : ∀ k : K, ρ k v₁ = (ϑ k : ℂ) • v₁ := hv₁P
  have hv₂M : ρ z⁻¹ v₁ ∉ relations ρ (M (j - 1)) := by
    intro hmem
    have h := apply_mem_relations ρ z (hzM j) hmem
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact hv₁M h
  have hv₂ : ∀ k : K, ρ (z⁻¹ * k * z) (ρ z⁻¹ v₁) = (ϑ k : ℂ) • ρ z⁻¹ v₁ := by
    intro k
    calc ρ (z⁻¹ * k * z) (ρ z⁻¹ v₁) = ρ z⁻¹ (ρ k v₁) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2
          group
      _ = (ϑ k : ℂ) • ρ z⁻¹ v₁ := by rw [hv₁ k, map_smul]
  obtain ⟨w, hwP, hwM⟩ := htransfer j _ hv₂ hv₂M
  exact fun hle => hwM (hle hwP)

end Langlands.Jacquet
