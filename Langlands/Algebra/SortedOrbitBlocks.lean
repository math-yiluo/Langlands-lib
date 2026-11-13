import Langlands.GroupScheme.Rational.SteinbergGaloisOrbitBlocks

/-! # Orbit blocks of a finite action sorted by an invariant key -/

noncomputable section

universe u v

set_option autoImplicit false

namespace Langlands.Algebra.FiniteActionOrbitBlocks

variable (Γ : Type v) [Group Γ] (I : Type u) [Finite I] [MulAction Γ I] (key : I → ℕ)

/-- The key of a block: the key of its first entry, and `0` for the empty list. -/
def blockKey (l : List I) : ℕ := (l.head?.map key).getD 0

/-- The orbit blocks, stably sorted by the keys of their first entries. -/
def sortedBlocks : List (List I) :=
  (blocks Γ I).mergeSort (fun l l' => decide (blockKey I key l ≤ blockKey I key l'))

theorem sortedBlocks_perm : (sortedBlocks Γ I key).Perm (blocks Γ I) :=
  List.mergeSort_perm _ _

theorem mem_sortedBlocks (l : List I) : l ∈ sortedBlocks Γ I key ↔ l ∈ blocks Γ I :=
  (sortedBlocks_perm Γ I key).mem_iff

theorem sortedBlocks_flatten_nodup : (sortedBlocks Γ I key).flatten.Nodup :=
  (sortedBlocks_perm Γ I key).flatten.nodup_iff.mpr (flatten_nodup Γ I)

theorem mem_sortedBlocks_flatten (i : I) : i ∈ (sortedBlocks Γ I key).flatten :=
  (sortedBlocks_perm Γ I key).flatten.mem_iff.mpr (mem_flatten Γ I i)

/-- The ordering of the finite set listing the sorted orbit blocks one after another. -/
def sortedOrdering : Fin (sortedBlocks Γ I key).flatten.length ≃ I := by
  classical
  exact List.Nodup.getEquivOfForallMemList _ (sortedBlocks_flatten_nodup Γ I key)
    (mem_sortedBlocks_flatten Γ I key)

theorem sortedBlocks_flatten_eq_ofFn :
    (sortedBlocks Γ I key).flatten = List.ofFn (sortedOrdering Γ I key) :=
  (List.ofFn_get _).symm

/-- Every sorted orbit block is invariant up to permutation under every group element. -/
theorem sortedBlocks_invariant (σ : Γ) (l : List I) (hl : l ∈ sortedBlocks Γ I key) :
    (l.map (fun i => σ • i)).Perm l :=
  blocks_invariant Γ I σ l ((mem_sortedBlocks Γ I key l).mp hl)

/-- Two entries of one sorted block belong to the same orbit. -/
theorem sortedBlocks_same_orbit (l : List I) (hl : l ∈ sortedBlocks Γ I key) (i j : I)
    (hi : i ∈ l) (hj : j ∈ l) : ∃ σ : Γ, σ • i = j :=
  same_orbit_of_mem_block Γ I l ((mem_sortedBlocks Γ I key l).mp hl) i j hi hj

variable {Γ I key}

theorem blockKey_eq (hkey : ∀ (σ : Γ) (i : I), key (σ • i) = key i) (l : List I)
    (hl : l ∈ sortedBlocks Γ I key) (i : I) (hi : i ∈ l) : blockKey I key l = key i := by
  cases l with
  | nil => simp at hi
  | cons a l' =>
    obtain ⟨σ, hσ⟩ := sortedBlocks_same_orbit Γ I key _ hl a i List.mem_cons_self hi
    simp only [blockKey, List.head?_cons, Option.map_some, Option.getD_some]
    rw [← hσ, hkey]

/-- For an invariant key, the entries of the sorted flattened list have weakly increasing
keys. -/
theorem sortedBlocks_flatten_pairwise (hkey : ∀ (σ : Γ) (i : I), key (σ • i) = key i) :
    (sortedBlocks Γ I key).flatten.Pairwise (fun i j => key i ≤ key j) := by
  have hsorted : (sortedBlocks Γ I key).Pairwise
      (fun l l' => decide (blockKey I key l ≤ blockKey I key l')) :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
      (fun a b => by
        rcases le_total (blockKey I key a) (blockKey I key b) with h | h <;> simp [h])
      _
  rw [List.pairwise_flatten]
  refine ⟨fun l hl => ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
      (fun _ _ => trivial))
    intro i j hi hj _
    rw [← blockKey_eq hkey l hl i hi, ← blockKey_eq hkey l hl j hj]
  · refine List.Pairwise.imp_of_mem ?_ hsorted
    intro l l' hl hl' h i hi j hj
    simp only [decide_eq_true_eq] at h
    rwa [← blockKey_eq hkey l hl i hi, ← blockKey_eq hkey l' hl' j hj]

/-- For an invariant key, entries of strictly smaller key come strictly earlier in the
sorted ordering. -/
theorem sortedOrdering_lt_of_key_lt (hkey : ∀ (σ : Γ) (i : I), key (σ • i) = key i)
    (j j' : Fin (sortedBlocks Γ I key).flatten.length)
    (h : key (sortedOrdering Γ I key j) < key (sortedOrdering Γ I key j')) : j < j' := by
  have hp := sortedBlocks_flatten_pairwise hkey
  rw [sortedBlocks_flatten_eq_ofFn, List.pairwise_ofFn] at hp
  rcases lt_trichotomy j j' with hjj | hjj | hjj
  · exact hjj
  · subst hjj
    exact absurd h (lt_irrefl _)
  · exact absurd (hp hjj) (not_le.mpr h)

end Langlands.Algebra.FiniteActionOrbitBlocks
