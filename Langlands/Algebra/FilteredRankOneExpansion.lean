import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Pi
import Mathlib.Order.Fin.Basic

/-! # Unique expansions from a filtration with rank-one graded pieces

A module with a finite decreasing filtration whose successive quotients are each zero or
free of rank one has unique expansions in lifts of the rank-one generators. The rank-one
condition is stated elementwise, without quotient modules.
-/

namespace Langlands.FilteredModule

variable {A X : Type*} [Ring A] [AddCommGroup X] [Module A X]

section

variable {n : ℕ} (K : Fin (n + 1) → Submodule A X) (S : Finset (Fin n)) (v : Fin n → X)

private theorem exists_expansion_aux
    (hn : K (Fin.last n) = ⊥)
    (huniq : ∀ j ∈ S, ∀ x ∈ K j.castSucc, ∃! a : A, x - a • v j ∈ K j.succ)
    (hzero : ∀ j ∉ S, K j.castSucc ≤ K j.succ) :
    ∀ i : ℕ, (hi : i ≤ n) → ∀ x ∈ K ⟨n - i, by omega⟩,
      ∃ a : Fin n → A, x = ∑ j ∈ S, a j • v j := by
  intro i
  induction i with
  | zero =>
    intro _ x hx
    have hx' : x ∈ K (Fin.last n) := hx
    rw [hn, Submodule.mem_bot] at hx'
    exact ⟨0, by simp [hx']⟩
  | succ i ih =>
    intro hi x hx
    let j : Fin n := ⟨n - (i + 1), by omega⟩
    have hjc : j.castSucc = ⟨n - (i + 1), by omega⟩ := rfl
    have hjs : j.succ = ⟨n - i, by omega⟩ := by
      ext
      simp only [Fin.val_succ, j]
      omega
    by_cases hj : j ∈ S
    · obtain ⟨c, hc, -⟩ := huniq j hj x (by rw [hjc]; exact hx)
      rw [hjs] at hc
      obtain ⟨a, ha⟩ := ih (by omega) _ hc
      refine ⟨a + Pi.single j c, ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      have hsingle : ∑ k ∈ S, (Pi.single j c : Fin n → A) k • v k = c • v j := by
        rw [Finset.sum_eq_single_of_mem j hj]
        · simp
        · intro k _ hk
          simp [hk]
      rw [hsingle, ← ha]
      exact (sub_add_cancel x _).symm
    · have hx' : x ∈ K j.succ := hzero j hj (by rw [hjc]; exact hx)
      rw [hjs] at hx'
      exact ih (by omega) x hx'

private theorem eq_zero_aux
    (hanti : Antitone K)
    (hmem : ∀ j ∈ S, v j ∈ K j.castSucc)
    (huniq : ∀ j ∈ S, ∀ x ∈ K j.castSucc, ∃! a : A, x - a • v j ∈ K j.succ)
    (a : Fin n → A) :
    ∀ i : ℕ, (hi : i ≤ n) → (∑ j ∈ S, a j • v j) ∈ K ⟨i, by omega⟩ →
      ∀ j ∈ S, (j : ℕ) < i → a j = 0 := by
  intro i
  induction i with
  | zero => intro _ _ j _ hj; omega
  | succ i ih =>
    intro hi hsum
    have hprev : (∑ j ∈ S, a j • v j) ∈ K ⟨i, by omega⟩ :=
      hanti (show (⟨i, by omega⟩ : Fin (n + 1)) ≤ ⟨i + 1, hi.trans_lt (Nat.lt_succ_self n)⟩ from
        Fin.mk_le_mk.mpr (Nat.le_succ i)) hsum
    have ih' := ih (by omega) hprev
    let j0 : Fin n := ⟨i, by omega⟩
    have hj0c : j0.castSucc = ⟨i, by omega⟩ := rfl
    have hj0s : j0.succ = ⟨i + 1, by omega⟩ := rfl
    have ha0 : j0 ∈ S → a j0 = 0 := by
      intro hj0
      have hrest : (∑ j ∈ S.erase j0, a j • v j) ∈ K j0.succ := by
        refine sum_mem fun j hj => ?_
        obtain ⟨hne, hjS⟩ := Finset.mem_erase.mp hj
        rcases lt_or_gt_of_ne (show (j : ℕ) ≠ i from fun h => hne (Fin.ext h)) with hlt | hgt
        · rw [ih' j hjS hlt, zero_smul]
          exact Submodule.zero_mem _
        · refine Submodule.smul_mem _ _ (hanti ?_ (hmem j hjS))
          rw [hj0s, Fin.le_def]
          simp only [Fin.val_castSucc]
          omega
      have hsplit := Finset.add_sum_erase S (fun j => a j • v j) hj0
      have hsingle : a j0 • v j0 ∈ K j0.succ := by
        have h := Submodule.sub_mem _ (show (∑ j ∈ S, a j • v j) ∈ K j0.succ by
          rw [hj0s]; exact hsum) hrest
        rwa [← hsplit, add_sub_cancel_right] at h
      have hx : a j0 • v j0 ∈ K j0.castSucc :=
        Submodule.smul_mem _ _ (hmem j0 hj0)
      obtain ⟨c, -, hcuniq⟩ := huniq j0 hj0 _ hx
      have h1 : a j0 = c := hcuniq (a j0) (by simp)
      have h2 : (0 : A) = c := hcuniq 0 (by simpa using hsingle)
      rw [h1, ← h2]
    intro j hjS hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact ih' j hjS hlt
    · have : j = j0 := Fin.ext heq
      subst this
      exact ha0 hjS

/-- Unique expansions from a finite decreasing filtration `K 0 = ⊤ ⊇ ⋯ ⊇ K n = ⊥` whose
step `j` (from `K j` to `K (j + 1)`) is either trivial, for `j ∉ S`, or free of rank one
on the class of `v j ∈ K j`, for `j ∈ S`: every element is uniquely `∑_{j ∈ S} a_j • v_j`. -/
theorem existsUnique_expansion
    (hanti : ∀ j : Fin n, K j.succ ≤ K j.castSucc) (h0 : K 0 = ⊤) (hn : K (Fin.last n) = ⊥)
    (hmem : ∀ j ∈ S, v j ∈ K j.castSucc)
    (huniq : ∀ j ∈ S, ∀ x ∈ K j.castSucc, ∃! a : A, x - a • v j ∈ K j.succ)
    (hzero : ∀ j ∉ S, K j.castSucc ≤ K j.succ) (x : X) :
    ∃! a : S → A, x = ∑ j : S, a j • v j := by
  have hA : Antitone K := Fin.antitone_iff_succ_le.mpr hanti
  obtain ⟨a, ha⟩ := exists_expansion_aux K S v hn huniq hzero n le_rfl x
    (by simp [h0])
  refine ⟨fun j => a j, ?_, ?_⟩
  · simpa only [Finset.sum_coe_sort S (fun j => a j • v j)] using ha
  · intro b hb
    funext j
    let b' : Fin n → A := fun k => if hk : k ∈ S then b ⟨k, hk⟩ else 0
    have hb' : x = ∑ k ∈ S, b' k • v k := by
      rw [hb, ← Finset.sum_coe_sort S (fun k => b' k • v k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [b', k.2]
    have hdiff : (∑ k ∈ S, (b' - a) k • v k) ∈ K ⟨n, by omega⟩ := by
      have : (∑ k ∈ S, (b' - a) k • v k) = 0 := by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hb', ← ha, sub_self]
      rw [this]
      exact Submodule.zero_mem _
    have h := eq_zero_aux K S v hA hmem huniq (b' - a) n le_rfl hdiff j j.2 j.1.2
    have : b' j = a j := sub_eq_zero.mp h
    simpa [b', j.2] using this

/-- The basis of `X` formed by the generators `v j`, `j ∈ S`, of the rank-one steps of a finite
decreasing filtration as in `existsUnique_expansion`. -/
noncomputable def basisOfFilteredRankOne
    (hanti : ∀ j : Fin n, K j.succ ≤ K j.castSucc) (h0 : K 0 = ⊤) (hn : K (Fin.last n) = ⊥)
    (hmem : ∀ j ∈ S, v j ∈ K j.castSucc)
    (huniq : ∀ j ∈ S, ∀ x ∈ K j.castSucc, ∃! a : A, x - a • v j ∈ K j.succ)
    (hzero : ∀ j ∉ S, K j.castSucc ≤ K j.succ) : Module.Basis S A X :=
  Module.Basis.mk (v := fun j : S => v j)
    (Fintype.linearIndependent_iff.mpr fun g hg j => by
      obtain ⟨a, -, ha⟩ := existsUnique_expansion K S v hanti h0 hn hmem huniq hzero 0
      have h1 : g = a := ha g hg.symm
      have h2 : (0 : S → A) = a := ha 0 (by simp)
      rw [h1, ← h2]
      rfl)
    (fun x _ => by
      obtain ⟨a, ha, -⟩ := existsUnique_expansion K S v hanti h0 hn hmem huniq hzero x
      rw [ha]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- The vectors of `basisOfFilteredRankOne` are the chosen generators. -/
theorem basisOfFilteredRankOne_apply
    (hanti : ∀ j : Fin n, K j.succ ≤ K j.castSucc) (h0 : K 0 = ⊤) (hn : K (Fin.last n) = ⊥)
    (hmem : ∀ j ∈ S, v j ∈ K j.castSucc)
    (huniq : ∀ j ∈ S, ∀ x ∈ K j.castSucc, ∃! a : A, x - a • v j ∈ K j.succ)
    (hzero : ∀ j ∉ S, K j.castSucc ≤ K j.succ) (j : S) :
    basisOfFilteredRankOne K S v hanti h0 hn hmem huniq hzero j = v j :=
  Module.Basis.mk_apply _ _ _

end

end Langlands.FilteredModule
