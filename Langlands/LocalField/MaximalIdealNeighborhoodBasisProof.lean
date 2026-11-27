import Langlands.LocalField.MaximalIdealNeighborhoodBasisStatement
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients

/-! # The maximal-ideal neighborhood basis of a local field -/

namespace Langlands.LocalField

universe u

theorem maximalIdealNeighborhoodBasis (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    MaximalIdealNeighborhoodBasisStatement F := by
  let O := FML.ringOfIntegers F
  let powers : ℕ → Set F := fun n =>
    (Subtype.val : O → F) '' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O)
  change (∀ n, IsCompact (powers n) ∧ IsOpen (powers n)) ∧
    (nhds (0 : F)).HasBasis (fun _ : ℕ => True) powers
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπne : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hlevels (n : ℕ) : IsCompact (powers n) ∧ IsOpen (powers n) := by
    let e := Homeomorph.mulLeft₀ ((π : F) ^ n) (pow_ne_zero n hπne)
    have heq : powers n = e '' (O : Set F) := by
      ext x
      change (∃ z : O, z ∈ IsLocalRing.maximalIdeal O ^ n ∧ (z : F) = x) ↔
        ∃ y : F, y ∈ (O : Set F) ∧ e y = x
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hz
        exact ⟨(y : F), y.property, by simp [e]⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨π ^ n * ⟨y, hy⟩, Ideal.mem_span_singleton.mpr ⟨_, rfl⟩, by simp [e]⟩
    rw [heq]
    exact ⟨(IsNonarchimedeanLocalField.isCompact_closedBall F 1).image e.continuous,
      e.isOpenMap _ ((ValuativeRel.valuation F).isOpen_integer)⟩
  refine ⟨hlevels, Filter.hasBasis_iff.mpr fun s => ⟨?_, ?_⟩⟩
  · intro hs
    have hs' : (Subtype.val : O → F) ⁻¹' s ∈ nhds (0 : O) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hs
    obtain ⟨n, hn⟩ := LocalFieldTheory.exists_maximalIdeal_pow_subset_nhds_zero F _ hs'
    exact ⟨n, trivial, Set.image_subset_iff.mpr hn⟩
  · rintro ⟨n, -, hn⟩
    have hz : (0 : F) ∈ powers n := ⟨0, Ideal.zero_mem _, rfl⟩
    exact Filter.mem_of_superset ((hlevels n).2.mem_nhds hz) hn

end Langlands.LocalField
