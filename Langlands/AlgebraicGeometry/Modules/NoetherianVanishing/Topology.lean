import Mathlib.Topology.KrullDimension

/-!
# An irreducible piece of a closed subset of a noetherian space

A nonempty closed subset `Z` of a noetherian topological space contains an irreducible closed
subset `T` together with an open set `O` such that `O ∩ Z` is a nonempty subset of `T`: write
`Z` as a finite union of irreducible closed subsets with as few members as possible, and take
for `O` the complement of the union of all members but one.

The height of an irreducible closed subset `T` in the poset of irreducible closed subsets is
the measure of dimension used in the vanishing induction: an irreducible closed subset that
misses a point of `T` and is contained in `T` has strictly smaller height.
-/

open TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Modules

namespace NoetherianVanishing

variable {X : Type*} [TopologicalSpace X]

/-- In a noetherian space, a nonempty closed set `Z` contains an irreducible closed set `T`
and meets some open set `O` in a nonempty subset of `T`. -/
theorem exists_irreducibleCloseds_inter_subset [NoetherianSpace X] (Z : Closeds X)
    (hZ : (Z : Set X).Nonempty) :
    ∃ (T : IrreducibleCloseds X) (O : Opens X), (T : Set X) ⊆ Z ∧
      ((O : Set X) ∩ Z).Nonempty ∧ (O : Set X) ∩ Z ⊆ T := by
  classical
  have hex : ∃ n, ∃ S : Finset (Closeds X), S.card = n ∧
      (∀ k ∈ S, IsIrreducible (k : Set X)) ∧ Z = S.sup id := by
    obtain ⟨S, hS, hZS⟩ := NoetherianSpace.exists_finset_irreducible Z
    exact ⟨S.card, S, rfl, fun k hk => hS ⟨k, hk⟩, hZS⟩
  obtain ⟨S, hcard, hS, hZS⟩ := Nat.find_spec hex
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    obtain ⟨x, hx⟩ := hZ
    rw [hZS] at hx
    simp at hx
  obtain ⟨T0, hT0⟩ := hSne
  have hsplit : S.sup id = T0 ⊔ (S.erase T0).sup id := by
    conv_lhs => rw [← Finset.insert_erase hT0]
    rw [Finset.sup_insert, id]
  have hnot : ¬ (T0 : Set X) ⊆ (((S.erase T0).sup id : Closeds X) : Set X) := by
    intro hsub
    have hZ' : Z = (S.erase T0).sup id := by
      rw [hZS, hsplit]
      exact sup_eq_right.2 hsub
    have hmin := Nat.find_min' hex ⟨S.erase T0, rfl,
      fun k hk => hS k (Finset.mem_of_mem_erase hk), hZ'⟩
    rw [Finset.card_erase_of_mem hT0] at hmin
    have hpos : 0 < S.card := Finset.card_pos.2 ⟨T0, hT0⟩
    omega
  obtain ⟨η, hηT, hηW⟩ := Set.not_subset.1 hnot
  have hT0Z : (T0 : Set X) ⊆ Z := by
    rw [hZS, hsplit, Closeds.coe_sup]
    exact Set.subset_union_left
  refine ⟨⟨T0, hS T0 hT0, T0.isClosed⟩, ((S.erase T0).sup id).compl, hT0Z,
    ⟨η, hηW, hT0Z hηT⟩, ?_⟩
  rintro x ⟨hxW, hxZ⟩
  rw [hZS, hsplit, Closeds.coe_sup] at hxZ
  rcases hxZ with hx | hx
  · exact hx
  · exact absurd hx hxW

/-- An irreducible closed subset of `T` missing a point of `T` has strictly smaller height. -/
theorem height_add_one_le_of_subset {T T' : IrreducibleCloseds X} (h : (T' : Set X) ⊆ T)
    {x : X} (hxT : x ∈ T) (hxT' : x ∉ T') : height T' + 1 ≤ height T :=
  height_add_one_le (lt_of_le_of_ne h (fun e => hxT' (e ▸ hxT)))

/-- The height of every irreducible closed subset is at most the dimension of the space. -/
theorem height_le_of_topologicalKrullDim_le {d : ℕ} (hX : topologicalKrullDim X ≤ d)
    (T : IrreducibleCloseds X) : height T ≤ d := by
  have h := (height_le_krullDim T).trans hX
  exact_mod_cast h

end NoetherianVanishing

end Langlands.AlgebraicGeometry.Modules
