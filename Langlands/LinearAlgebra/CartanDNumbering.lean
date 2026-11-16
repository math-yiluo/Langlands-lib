import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.GroupTheory.Perm.Fin

/-! # Symmetries of the numbered Cartan matrix of type D -/

namespace Langlands.CartanDNumbering

/-- Interchange the two fork tips of the standard type-D numbering. -/
def forkSwap (n : ℕ) (hn : 2 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩

theorem eq_two_iff {n : ℕ} (i j : Fin n) :
    CartanMatrix.D n i j = 2 ↔ i = j := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> simp_all

theorem eq_neg_one_iff {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    CartanMatrix.D n i j = -1 ↔
      (i.val + 1 = j.val ∧ j.val + 2 < n) ∨
      (j.val + 1 = i.val ∧ i.val + 2 < n) ∨
      (i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n)) ∨
      (j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n)) := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> constructor <;> intro h <;> first | omega | simp_all

theorem injective_of_preserves {n : ℕ} (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.D n (f i) (f j) = CartanMatrix.D n i j) :
    Function.Injective f := by
  intro i j hij
  apply (eq_two_iff i j).mp
  rw [← hf, hij]
  exact (eq_two_iff _ _).mpr rfl

/-- The fork center is the only vertex with three distinct neighbors. -/
theorem eq_center_of_three_neighbors {n : ℕ} (hn : 4 ≤ n)
    (i a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : CartanMatrix.D n i a = -1) (hb : CartanMatrix.D n i b = -1)
    (hc : CartanMatrix.D n i c = -1) : i.val + 3 = n := by
  rw [eq_neg_one_iff hn] at ha hb hc
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  omega

/-- Each of the two short fork tips has just the fork center as neighbor. -/
theorem neighbor_of_tip {n : ℕ} (hn : 4 ≤ n) (i j : Fin n)
    (hi : i.val + 2 = n ∨ i.val + 1 = n)
    (hij : CartanMatrix.D n i j = -1) : j.val + 3 = n := by
  rw [eq_neg_one_iff hn] at hij
  omega

/-- Every type-D Cartan symmetry fixes the fork center, including in rank four. -/
theorem fixes_center {n : ℕ} (hn : 4 ≤ n) (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.D n (f i) (f j) = CartanMatrix.D n i j) :
    f ⟨n - 3, by omega⟩ = ⟨n - 3, by omega⟩ := by
  have hinj := injective_of_preserves f hf
  let i : Fin n := ⟨n - 3, by omega⟩
  let a : Fin n := ⟨n - 4, by omega⟩
  let b : Fin n := ⟨n - 2, by omega⟩
  let c : Fin n := ⟨n - 1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  have hac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [a, c] at this; omega
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b, c] at this; omega
  have hedge : ∀ j : Fin n, j = a ∨ j = b ∨ j = c →
      CartanMatrix.D n i j = -1 := by
    intro j hj
    rw [eq_neg_one_iff hn]
    rcases hj with rfl | rfl | rfl <;> dsimp [i, a, b, c] <;> omega
  have h := eq_center_of_three_neighbors hn (f i) (f a) (f b) (f c)
    (hinj.ne hab) (hinj.ne hac) (hinj.ne hbc)
    (by rw [hf]; exact hedge a (Or.inl rfl))
    (by rw [hf]; exact hedge b (Or.inr (Or.inl rfl)))
    (by rw [hf]; exact hedge c (Or.inr (Or.inr rfl)))
  apply Fin.ext
  change (f i).val = n - 3
  omega

/-- In ranks at least five every vertex outside the two fork tips is fixed. -/
theorem fixes_nonfork {n : ℕ} (hn : 5 ≤ n) (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.D n (f i) (f j) = CartanMatrix.D n i j)
    (i : Fin n) (hi : i.val + 2 < n) : f i = i := by
  have hn4 : 4 ≤ n := by omega
  have hinj := injective_of_preserves f hf
  let center : Fin n := ⟨n - 3, by omega⟩
  let prev : Fin n := ⟨n - 4, by omega⟩
  let prev' : Fin n := ⟨n - 5, by omega⟩
  have hc : f center = center := fixes_center hn4 f hf
  have hprev : f prev = prev := by
    have hp : CartanMatrix.D n (f prev) center = -1 := by
      rw [← hc, hf, eq_neg_one_iff hn4]
      dsimp [prev, center]
      omega
    have hprev' : CartanMatrix.D n (f prev) (f prev') = -1 := by
      rw [hf, eq_neg_one_iff hn4]
      dsimp [prev, prev']
      omega
    have hnot : ¬ ((f prev).val + 2 = n ∨ (f prev).val + 1 = n) := by
      intro htip
      have h := neighbor_of_tip hn4 (f prev) (f prev') htip hprev'
      have heq : f prev' = f center := by
        rw [hc]
        apply Fin.ext
        dsimp [center]
        omega
      have heq' := congrArg Fin.val (hinj heq)
      dsimp [prev', center] at heq'
      omega
    rw [eq_neg_one_iff hn4] at hp
    apply Fin.ext
    dsimp [prev, center] at *
    omega
  have hfix : ∀ k, ∀ j : Fin n, j.val + 2 < n →
      n - 3 - j.val = k → f j = j := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hj hk
      by_cases hjc : j = center
      · simpa [hjc] using hc
      by_cases hjp : j = prev
      · simpa [hjp] using hprev
      have hjc' : j.val ≠ n - 3 := fun h => hjc (Fin.ext h)
      have hjp' : j.val ≠ n - 4 := fun h => hjp (Fin.ext h)
      let next : Fin n := ⟨j.val + 1, by omega⟩
      let next' : Fin n := ⟨j.val + 2, by omega⟩
      have hnext : f next = next := ih (n - 3 - next.val)
        (by dsimp [next]; omega) next (by dsimp [next]; omega) rfl
      have hnext' : f next' = next' := ih (n - 3 - next'.val)
        (by dsimp [next']; omega) next' (by dsimp [next']; omega) rfl
      have hadj : CartanMatrix.D n (f j) next = -1 := by
        rw [← hnext, hf, eq_neg_one_iff hn4]
        dsimp [next]
        omega
      have hne : f j ≠ next' := by
        rw [← hnext']
        intro h
        have := congrArg Fin.val (hinj h)
        dsimp [next'] at this
        omega
      have hne' : (f j).val ≠ next'.val := fun h => hne (Fin.ext h)
      rw [eq_neg_one_iff hn4] at hadj
      apply Fin.ext
      dsimp [next, next'] at *
      omega
  exact hfix _ i hi rfl

/-- Once all nonfork vertices are fixed, the remaining symmetry is one global
choice between identity and interchanging the two fork tips. -/
theorem eq_id_or_swap_of_fixes_nonfork {n : ℕ} (hn : 4 ≤ n) (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.D n (f i) (f j) = CartanMatrix.D n i j)
    (hfix : ∀ i : Fin n, i.val + 2 < n → f i = i) :
    (∀ i, f i = i) ∨
      ∀ i, f i = Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ i := by
  have hinj := injective_of_preserves f hf
  let a : Fin n := ⟨n - 2, by omega⟩
  let b : Fin n := ⟨n - 1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  have him : ∀ i : Fin n, i = a ∨ i = b → f i = a ∨ f i = b := by
    intro i hi
    have houtside : ¬ (f i).val + 2 < n := by
      intro hlt
      have hsame := hinj (hfix (f i) hlt)
      have hval := congrArg Fin.val hsame
      rcases hi with rfl | rfl <;> dsimp [a, b] at * <;> omega
    have hlt := (f i).isLt
    have hval : (f i).val = a.val ∨ (f i).val = b.val := by
      dsimp [a, b]
      omega
    exact hval.imp Fin.ext Fin.ext
  rcases him a (Or.inl rfl) with ha | ha
  · have hb : f b = b := (him b (Or.inr rfl)).resolve_left
      (fun h => hab (hinj (ha.trans h.symm)))
    left
    intro i
    by_cases hi : i.val + 2 < n
    · exact hfix i hi
    · have hlt := i.isLt
      have hval : i = a ∨ i = b := by
        apply (show i.val = a.val ∨ i.val = b.val from by dsimp [a, b]; omega).imp
          Fin.ext Fin.ext
      rcases hval with rfl | rfl <;> assumption
  · have hb : f b = a := (him b (Or.inr rfl)).resolve_right
      (fun h => hab (hinj (ha.trans h.symm)))
    right
    intro i
    change f i = Equiv.swap a b i
    by_cases hia : i = a
    · subst i
      simpa using ha
    by_cases hib : i = b
    · subst i
      simpa using hb
    rw [Equiv.swap_apply_of_ne_of_ne hia hib]
    apply hfix
    have hlt := i.isLt
    have hia' : i.val ≠ a.val := fun h => hia (Fin.ext h)
    have hib' : i.val ≠ b.val := fun h => hib (Fin.ext h)
    dsimp [a, b] at *
    omega

/-- The only type-D Cartan symmetries in ranks at least five are identity
and the transposition of the two fork tips. -/
theorem eq_id_or_swap_of_preserves {n : ℕ} (hn : 5 ≤ n) (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.D n (f i) (f j) = CartanMatrix.D n i j) :
    (∀ i, f i = i) ∨
      ∀ i, f i = Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ i :=
  eq_id_or_swap_of_fixes_nonfork (by omega) f hf (fixes_nonfork hn f hf)

/-- The full symmetry bound in terms of the named fork permutation. -/
theorem eq_id_or_forkSwap_of_preserves {n : ℕ} (hn : 5 ≤ n) (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.D n (f i) (f j) = CartanMatrix.D n i j) :
    (∀ i, f i = i) ∨ (∀ i, f i = forkSwap n (by omega) i) :=
  eq_id_or_swap_of_preserves hn f hf

end Langlands.CartanDNumbering
