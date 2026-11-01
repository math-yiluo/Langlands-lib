import Langlands.Representation.Geometric.WeylDefinitions

/-! Two-sided Weyl support cores used in the corrected Aubert filtration. -/

namespace Langlands.Aubert.Support

universe u

variable {G : Type u} [Group G]

/-- A subset invariant under the two subgroup actions. -/
def IsTwoSidedInvariant (H K : Subgroup G) (θ : Set G) : Prop :=
  ∀ w ∈ θ, ∀ h ∈ H, ∀ k ∈ K, h * w * k ∈ θ

/-- The largest subset of `θ` invariant on the left by `H` and on the right
by `K`: an entire double coset must lie in `θ`. -/
def twoSidedCore (H K : Subgroup G) (θ : Set G) : Set G :=
  {w | DoubleCoset.doubleCoset w H K ⊆ θ}

variable (H K : Subgroup G)

theorem mem_twoSidedCore_iff (θ : Set G) (w : G) :
    w ∈ twoSidedCore H K θ ↔
      ∀ h ∈ H, ∀ k ∈ K, h * w * k ∈ θ := by
  constructor
  · intro hw h hh k hk
    exact hw (DoubleCoset.mem_doubleCoset.mpr ⟨h, hh, k, hk, rfl⟩)
  · intro hw x hx
    obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    exact hw h hh k hk

theorem twoSidedCore_subset (θ : Set G) :
    twoSidedCore H K θ ⊆ θ :=
  fun w hw => hw (DoubleCoset.mem_doubleCoset_self H K w)

theorem mem_twoSidedCore_iff_of_mem_doubleCoset (θ : Set G) {w v : G}
    (hv : v ∈ DoubleCoset.doubleCoset w H K) :
    v ∈ twoSidedCore H K θ ↔ w ∈ twoSidedCore H K θ := by
  change (DoubleCoset.doubleCoset v H K ⊆ θ) ↔
    (DoubleCoset.doubleCoset w H K ⊆ θ)
  rw [DoubleCoset.doubleCoset_eq_of_mem hv]

theorem twoSidedCore_invariant (θ : Set G) :
    IsTwoSidedInvariant H K (twoSidedCore H K θ) := by
  intro w hw h hh k hk
  exact (mem_twoSidedCore_iff_of_mem_doubleCoset H K θ
    (DoubleCoset.mem_doubleCoset.mpr ⟨h, hh, k, hk, rfl⟩)).mpr hw

theorem subset_twoSidedCore {S θ : Set G} (hS : S ⊆ θ)
    (hInv : IsTwoSidedInvariant H K S) :
    S ⊆ twoSidedCore H K θ := by
  intro w hw
  apply (mem_twoSidedCore_iff H K θ w).mpr
  intro h hh k hk
  exact hS (hInv w hw h hh k hk)

theorem twoSidedCore_eq_self_iff (θ : Set G) :
    twoSidedCore H K θ = θ ↔ IsTwoSidedInvariant H K θ := by
  constructor
  · intro h
    rw [← h]
    exact twoSidedCore_invariant H K θ
  · intro h
    exact Set.Subset.antisymm (twoSidedCore_subset H K θ)
      (subset_twoSidedCore H K (fun _ hx => hx) h)

@[simp] theorem twoSidedCore_idem (θ : Set G) :
    twoSidedCore H K (twoSidedCore H K θ) = twoSidedCore H K θ :=
  (twoSidedCore_eq_self_iff H K _).mpr (twoSidedCore_invariant H K θ)

theorem twoSidedCore_mono {θ η : Set G} (hθη : θ ⊆ η) :
    twoSidedCore H K θ ⊆ twoSidedCore H K η :=
  fun _ hw _ hv => hθη (hw hv)

theorem twoSidedCore_antitone_subgroups {H' K' : Subgroup G}
    (hH : H' ≤ H) (hK : K' ≤ K) (θ : Set G) :
    twoSidedCore H K θ ⊆ twoSidedCore H' K' θ := by
  intro w hw
  apply (mem_twoSidedCore_iff H' K' θ w).mpr
  intro h hh k hk
  exact (mem_twoSidedCore_iff H K θ w).mp hw h (hH hh) k (hK hk)

@[simp] theorem twoSidedCore_empty :
    twoSidedCore H K (∅ : Set G) = ∅ := by
  exact Set.Subset.antisymm (twoSidedCore_subset H K ∅) (Set.empty_subset _)

@[simp] theorem twoSidedCore_univ :
    twoSidedCore H K (Set.univ : Set G) = Set.univ := by
  ext w
  simp [twoSidedCore]

@[simp] theorem twoSidedCore_inter (θ η : Set G) :
    twoSidedCore H K (θ ∩ η) =
      twoSidedCore H K θ ∩ twoSidedCore H K η := by
  ext w
  exact ⟨fun h => ⟨fun _ hx => (h hx).1, fun _ hx => (h hx).2⟩,
    fun h _ hx => ⟨h.1 hx, h.2 hx⟩⟩

private theorem mem_doubleCoset_symm {w v : G}
    (hv : v ∈ DoubleCoset.doubleCoset w H K) :
    w ∈ DoubleCoset.doubleCoset v H K := by
  rw [DoubleCoset.doubleCoset_eq_of_mem hv]
  exact DoubleCoset.mem_doubleCoset_self H K w

/-- Removing one point from a support removes its whole double coset from
the two-sided core. No length or minimal-representative assertion is used. -/
theorem twoSidedCore_diff_singleton (θ : Set G) (w : G) :
    twoSidedCore H K (θ \ {w}) =
      twoSidedCore H K θ \ DoubleCoset.doubleCoset w H K := by
  ext v
  constructor
  · intro hv
    refine ⟨fun x hx => (hv hx).1, ?_⟩
    intro hvw
    exact (hv (mem_doubleCoset_symm H K hvw)).2 rfl
  · rintro ⟨hv, hvw⟩ x hx
    refine ⟨hv hx, ?_⟩
    intro hxw
    have hw : w ∈ DoubleCoset.doubleCoset v H K := by
      simpa only [Set.mem_singleton_iff.mp hxw] using hx
    exact hvw (mem_doubleCoset_symm H K hw)

/-- A singleton removal changes the core exactly when the removed point was
already in that core. -/
theorem twoSidedCore_diff_singleton_ne_iff (θ : Set G) (w : G) :
    twoSidedCore H K θ ≠ twoSidedCore H K (θ \ {w}) ↔
      w ∈ twoSidedCore H K θ := by
  rw [twoSidedCore_diff_singleton]
  constructor
  · intro h
    by_contra hw
    apply h
    ext v
    constructor
    · intro hv
      refine ⟨hv, ?_⟩
      intro hvw
      exact hw ((mem_twoSidedCore_iff_of_mem_doubleCoset H K θ hvw).mp hv)
    · exact fun hv => hv.1
  · intro hw heq
    have h := heq ▸ hw
    exact h.2 (DoubleCoset.mem_doubleCoset_self H K w)

/-- In the nonzero singleton step, the entire removed double coset is the
difference of the two invariant supports. -/
theorem twoSidedCore_singleton_step (θ : Set G) (w : G)
    (hw : w ∈ twoSidedCore H K θ) :
    twoSidedCore H K θ \ twoSidedCore H K (θ \ {w}) =
      DoubleCoset.doubleCoset w H K := by
  rw [twoSidedCore_diff_singleton]
  ext v
  constructor
  · rintro ⟨hv, hv'⟩
    by_contra hvw
    exact hv' ⟨hv, hvw⟩
  · intro hvw
    refine ⟨(mem_twoSidedCore_iff_of_mem_doubleCoset H K θ hvw).mpr hw, ?_⟩
    exact fun hv => hv.2 hvw

/-- The set-theoretic minimality step in the corrected support argument.
If every remaining point has rank at least that of `w`, then a changed
two-sided core forces `w` to have minimum rank on its entire double coset. -/
theorem singleton_drop_forces_minimal {α : Type*} [Preorder α]
    (rank : G → α) (θ : Set G) (w : G)
    (hTail : ∀ v ∈ θ \ {w}, rank w ≤ rank v)
    (hChange : twoSidedCore H K θ ≠ twoSidedCore H K (θ \ {w})) :
    ∀ v ∈ DoubleCoset.doubleCoset w H K, rank w ≤ rank v := by
  have hw := (twoSidedCore_diff_singleton_ne_iff H K θ w).mp hChange
  intro v hv
  by_cases hvw : v = w
  · simpa only [hvw] using (le_refl (rank w))
  · exact hTail v ⟨hw hv, hvw⟩

section BlockWeyl

open GeneralLinear Geometric

variable {n : ℕ}

/-- In the Library's convention a representative for source `B` and target
`C` lies in `W_C \ W / W_B`. Both actions enter the corrected support. -/
def weylSupport (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n))) :
    Set (Equiv.Perm (Fin n)) :=
  twoSidedCore (blockWeyl C) (blockWeyl B) θ

theorem weylSupport_invariant (B C : BlockShape n)
    (θ : Set (Equiv.Perm (Fin n))) :
    IsTwoSidedInvariant (blockWeyl C) (blockWeyl B) (weylSupport B C θ) :=
  twoSidedCore_invariant _ _ _

theorem weylSupport_singleton_step (B C : BlockShape n)
    (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
    (hw : w ∈ weylSupport B C θ) :
    weylSupport B C θ \ weylSupport B C (θ \ {w}) =
      DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B) :=
  twoSidedCore_singleton_step _ _ θ w hw

end BlockWeyl

end Langlands.Aubert.Support
