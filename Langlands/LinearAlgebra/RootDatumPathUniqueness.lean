import Langlands.LinearAlgebra.RootDatumPathWeights

/-! # Uniqueness of path enumerations of a Dynkin component -/

noncomputable section

open Set Function

set_option autoImplicit false

namespace Langlands.LinearAlgebra.RootDatumPathWeights

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootDatum ι M N} {b : P.Base}

/-- A simple root that is not orthogonal to a vertex of a path component lies on the path. -/
theorem IsPathComponent.mem_range_of_pairing_ne_zero {L : ℕ} {β : Fin L → b.support}
    (hβ : IsPathComponent β) {z : b.support} (i : Fin L)
    (h : P.pairing (z : ι) (β i : ι) ≠ 0) : z ∈ Set.range β := by
  by_contra hz
  exact h (hβ.isOrthogonal z hz i).1

/-- Consecutive vertices of a path are not orthogonal. -/
theorem IsPathComponent.pairing_succ_ne_zero {L : ℕ} {β : Fin L → b.support}
    (hβ : IsPathComponent β) {j : ℕ} (hj : j + 1 < L) :
    P.pairing (β ⟨j + 1, hj⟩ : ι) (β ⟨j, by omega⟩ : ι) ≠ 0 := by
  rw [hβ.pairing_succ_left hj]
  norm_num

/-- Consecutive vertices of a path are not orthogonal, in the other order. -/
theorem IsPathComponent.pairing_pred_ne_zero {L : ℕ} {β : Fin L → b.support}
    (hβ : IsPathComponent β) {j : ℕ} (hj : j + 1 < L) :
    P.pairing (β ⟨j, by omega⟩ : ι) (β ⟨j + 1, hj⟩ : ι) ≠ 0 := by
  rw [hβ.pairing_succ_right hj]
  norm_num

/-- If one vertex of a path component lies on another path component, then the whole
first path lies on the second. -/
theorem IsPathComponent.range_subset {L L' : ℕ} {β : Fin L → b.support}
    {β' : Fin L' → b.support} (hβ : IsPathComponent β) (hβ' : IsPathComponent β')
    {i' : Fin L'} (h : β' i' ∈ Set.range β) : Set.range β' ⊆ Set.range β := by
  have hup : ∀ d : ℕ, ∀ hd : (i' : ℕ) + d < L', β' ⟨i' + d, hd⟩ ∈ Set.range β := by
    intro d
    induction d with
    | zero => intro hd; simpa using h
    | succ d ih =>
      intro hd
      obtain ⟨j, hj⟩ := ih (by omega)
      apply hβ.mem_range_of_pairing_ne_zero j
      rw [hj]
      exact hβ'.pairing_succ_ne_zero (j := (i' : ℕ) + d) (by omega)
  have hdown : ∀ d : ℕ, ∀ hd : d ≤ (i' : ℕ), β' ⟨i' - d, by omega⟩ ∈ Set.range β := by
    intro d
    induction d with
    | zero => intro hd; simpa using h
    | succ d ih =>
      intro hd
      obtain ⟨j, hj⟩ := ih (by omega)
      apply hβ.mem_range_of_pairing_ne_zero j
      rw [hj]
      have := hβ'.pairing_pred_ne_zero (j := (i' : ℕ) - (d + 1)) (by omega)
      simpa only [show (i' : ℕ) - (d + 1) + 1 = i' - d by omega] using this
  rintro _ ⟨j, rfl⟩
  by_cases hj : (i' : ℕ) ≤ j
  · have := hup ((j : ℕ) - i') (by omega)
    simpa only [show (i' : ℕ) + (j - i') = j by omega] using this
  · have := hdown ((i' : ℕ) - j) (by omega)
    simpa only [show (i' : ℕ) - (i' - j) = j by omega] using this

/-- Two path components sharing a vertex have the same range. -/
theorem IsPathComponent.range_eq {L L' : ℕ} {β : Fin L → b.support}
    {β' : Fin L' → b.support} (hβ : IsPathComponent β) (hβ' : IsPathComponent β')
    {i : Fin L} {i' : Fin L'} (h : β i = β' i') : Set.range β' = Set.range β :=
  le_antisymm (hβ.range_subset hβ' ⟨i, h⟩) (hβ'.range_subset hβ ⟨i', h.symm⟩)

/-- Two path components sharing a vertex have the same length. -/
theorem IsPathComponent.length_eq {L L' : ℕ} {β : Fin L → b.support}
    {β' : Fin L' → b.support} (hβ : IsPathComponent β) (hβ' : IsPathComponent β')
    {i : Fin L} {i' : Fin L'} (h : β i = β' i') : L' = L := by
  have hr := hβ.range_eq hβ' h
  have e : Fin L' ≃ Fin L :=
    (Equiv.ofInjective β' hβ'.injective).trans
      ((Equiv.subtypeEquivRight (fun x => by rw [hr])).trans (Equiv.ofInjective β hβ.injective).symm)
  simpa using Fintype.card_congr e

/-- Integer bookkeeping for an injective walk with unit steps: such a walk on `Fin L`
visiting `L` points is either the identity or the reversal. -/
theorem walk_eq_id_or_rev {L : ℕ} (π : Fin L → Fin L) (hπ : Function.Injective π)
    (hstep : ∀ (j : ℕ) (hj : j + 1 < L),
      (π ⟨j, by omega⟩ : ℕ) + 1 = π ⟨j + 1, hj⟩ ∨ (π ⟨j + 1, hj⟩ : ℕ) + 1 = π ⟨j, by omega⟩) :
    (∀ j : Fin L, (π j : ℕ) = j) ∨ (∀ j : Fin L, (π j : ℕ) = L - 1 - j) := by
  -- transfer everything to a function `ℕ → ℕ`
  let f : ℕ → ℕ := fun j => if h : j < L then (π ⟨j, h⟩ : ℕ) else 0
  have hfj : ∀ j : Fin L, f j = π j := fun j => by simp [f, j.2]
  have hflt : ∀ j, j < L → f j < L := fun j hj => by
    simp only [f, hj, ↓reduceDIte]; exact (π _).2
  have hfinj : ∀ j j', j < L → j' < L → f j = f j' → j = j' := by
    intro j j' hj hj' h
    simp only [f, hj, hj', ↓reduceDIte] at h
    have := hπ (Fin.ext h)
    simpa using this
  have hfstep : ∀ j, j + 1 < L → f j + 1 = f (j + 1) ∨ f (j + 1) + 1 = f j := by
    intro j hj
    simp only [f, hj, show j < L by omega, ↓reduceDIte]
    exact hstep j hj
  rcases Nat.lt_or_ge L 2 with hL | hL
  · left
    intro j
    have h1 := (π j).2
    have h2 := j.2
    omega
  rcases hfstep 0 (by omega) with h0 | h0
  · -- increasing walk
    have hinc : ∀ j, j + 1 < L → f j + 1 = f (j + 1) := by
      intro j
      induction j with
      | zero => intro _; exact h0
      | succ j ih =>
        intro hj
        rcases hfstep (j + 1) hj with h | h
        · exact h
        · exfalso
          have h' := ih (by omega)
          have := hfinj j (j + 1 + 1) (by omega) hj (by omega)
          omega
    have hval : ∀ j, j < L → f j = f 0 + j := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        rw [← hinc j hj, ih (by omega)]
        omega
    left
    intro j
    have hlast := hval (L - 1) (by omega)
    have hb := hflt (L - 1) (by omega)
    have := hval j j.2
    rw [← hfj j]
    omega
  · -- decreasing walk
    have hdec : ∀ j, j + 1 < L → f (j + 1) + 1 = f j := by
      intro j
      induction j with
      | zero => intro _; exact h0
      | succ j ih =>
        intro hj
        rcases hfstep (j + 1) hj with h | h
        · exfalso
          have h' := ih (by omega)
          have := hfinj j (j + 1 + 1) (by omega) hj (by omega)
          omega
        · exact h
    have hval : ∀ j, j < L → f j + j = f 0 := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        rw [← ih (by omega), ← hdec j hj]
        omega
    right
    intro j
    have hfirst := hflt 0 (by omega)
    have hlast := hval (L - 1) (by omega)
    have := hval j j.2
    rw [← hfj j]
    omega

/-- **Uniqueness of path enumerations.** Two path components sharing a vertex have the
same length, and the second enumeration is the first one or its reversal. -/
theorem IsPathComponent.eq_or_eq_rev {L L' : ℕ} {β : Fin L → b.support}
    {β' : Fin L' → b.support} (hβ : IsPathComponent β) (hβ' : IsPathComponent β')
    {i : Fin L} {i' : Fin L'} (h : β i = β' i') :
    L' = L ∧ ((∀ j : Fin L', β' j = β (Fin.cast (hβ.length_eq hβ' h) j)) ∨
      (∀ j : Fin L', β' j = β (Fin.rev (Fin.cast (hβ.length_eq hβ' h) j)))) := by
  have hL := hβ.length_eq hβ' h
  subst hL
  refine ⟨rfl, ?_⟩
  have hr := hβ.range_eq hβ' h
  have hmem : ∀ j, β' j ∈ Set.range β := fun j => hr ▸ Set.mem_range_self j
  let π : Fin L' → Fin L' := fun j => (hmem j).choose
  have hπ : ∀ j, β (π j) = β' j := fun j => (hmem j).choose_spec
  have hπinj : Function.Injective π := by
    intro j j' hjj
    apply hβ'.injective
    rw [← hπ j, ← hπ j', hjj]
  have hstep : ∀ (j : ℕ) (hj : j + 1 < L'),
      (π ⟨j, by omega⟩ : ℕ) + 1 = π ⟨j + 1, hj⟩ ∨
        (π ⟨j + 1, hj⟩ : ℕ) + 1 = π ⟨j, by omega⟩ := by
    intro j hj
    have hp := hβ.pairing_eq (π ⟨j + 1, hj⟩) (π ⟨j, by omega⟩)
    rw [hπ, hπ, hβ'.pairing_succ_left hj] at hp
    split_ifs at hp with h1 h2
    exact h2.symm
  rcases walk_eq_id_or_rev π hπinj hstep with hid | hrev
  · left
    intro j
    rw [← hπ j]
    congr 1
    ext
    simp [hid j]
  · right
    intro j
    rw [← hπ j]
    congr 1
    ext
    simp [hrev j]
    omega

/-- A pairing-preserving permutation of the simple roots carries path components to path
components. -/
theorem IsPathComponent.comp_perm {L : ℕ} {β : Fin L → b.support} (hβ : IsPathComponent β)
    (σ : Equiv.Perm b.support)
    (hσ : ∀ u v : b.support, P.pairing (σ u : ι) (σ v : ι) = P.pairing (u : ι) (v : ι)) :
    IsPathComponent (fun i => σ (β i)) := by
  refine ⟨hβ.pos, fun i j => by rw [hσ]; exact hβ.pairing_eq i j, ?_⟩
  intro z hz i
  have hz' : σ.symm z ∉ Set.range β := by
    rintro ⟨j, hj⟩
    exact hz ⟨j, by simp [hj]⟩
  have ho := hβ.isOrthogonal (σ.symm z) hz' i
  have h1 := hσ (σ.symm z) (β i)
  have h2 := hσ (β i) (σ.symm z)
  rw [Equiv.apply_symm_apply] at h1 h2
  exact ⟨h1.trans ho.1, h2.trans ho.2⟩

end Langlands.LinearAlgebra.RootDatumPathWeights
