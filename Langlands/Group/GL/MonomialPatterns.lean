import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-! # Labelled permutations that reverse consecutive blocks -/

noncomputable section

namespace Langlands.GeneralLinear

/-- Ascending pairs preserve adjacency in both directions. Adjacent ascents preserve the label. -/
def IsMonomialPattern {n : ℕ} {α : Type*} (w : Equiv.Perm (Fin n)) (d : Fin n → α) : Prop :=
  ∀ i j : Fin n, i < j → w i < w j →
    (i.val + 1 = j.val ↔ (w i).val + 1 = (w j).val) ∧ (i.val + 1 = j.val → d i = d j)

/-- A permutation and a compatible list of labels. -/
abbrev MonomialPattern (n : ℕ) (α : Type*) :=
  {p : Equiv.Perm (Fin n) × (Fin n → α) // IsMonomialPattern p.1 p.2}

namespace MonomialPattern

variable {α : Type*}

private theorem le_of_step {m : ℕ} (f : Fin m → Fin m)
    (hs : ∀ i j, i.val + 1 = j.val → (f j).val ≤ (f i).val + 1)
    {i j : Fin m} (hij : i ≤ j) : (f j).val + i.val ≤ (f i).val + j.val := by
  have aux : ∀ t : ℕ, i.val ≤ t → ∀ ht : t < m, (f ⟨t, ht⟩).val + i.val ≤ (f i).val + t := by
    intro t hit
    induction t, hit using Nat.le_induction with
    | base => intro hi; rfl
    | succ t hit ih =>
      intro ht
      have h := hs ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl
      have hi := ih (by omega)
      omega
  exact aux j.val hij j.isLt

private theorem forward_step {m : ℕ} {w : Equiv.Perm (Fin m)} {d : Fin m → α}
    (h : IsMonomialPattern w d) : ∀ i j, i.val + 1 = j.val → (w j).val ≤ (w i).val + 1 := by
  intro i j hij
  by_cases hw : w i < w j
  · have he := (h i j (show i < j by exact Fin.lt_def.mpr (by omega)) hw).1.mp hij
    omega
  · exact (Fin.le_def.mp (le_of_not_gt hw)).trans (Nat.le_add_right _ _)

private theorem inverse_step {m : ℕ} {w : Equiv.Perm (Fin m)} {d : Fin m → α}
    (h : IsMonomialPattern w d) :
    ∀ i j, i.val + 1 = j.val → (w.symm j).val ≤ (w.symm i).val + 1 := by
  intro i j hij
  by_cases hw : w.symm i < w.symm j
  · have hlt : w (w.symm i) < w (w.symm j) := by
      simpa only [Equiv.apply_symm_apply] using Fin.lt_def.mpr (show i.val < j.val by omega)
    have he := (h _ _ hw hlt).1.mpr (by simpa only [Equiv.apply_symm_apply] using hij)
    omega
  · exact (Fin.le_def.mp (le_of_not_gt hw)).trans (Nat.le_add_right _ _)

private theorem firstBlock {n : ℕ} (w : Equiv.Perm (Fin (n + 1))) {d : Fin (n + 1) → α}
    (h : IsMonomialPattern w d) {i : Fin (n + 1)} (hi : i ≤ w.symm (Fin.last n)) :
    (w i).val + (w.symm (Fin.last n)).val = n + i.val := by
  have h₁ := le_of_step w (forward_step h) hi
  have h₂ := le_of_step w.symm (inverse_step h) (Fin.le_last (w i))
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Fin.val_last] at h₁ h₂
  omega

private theorem firstBlock_labels {n : ℕ} (w : Equiv.Perm (Fin (n + 1))) {d : Fin (n + 1) → α}
    (h : IsMonomialPattern w d) {i : Fin (n + 1)} (hi : i ≤ w.symm (Fin.last n)) : d i = d 0 := by
  have aux : ∀ j : ℕ, ∀ hj : j ≤ (w.symm (Fin.last n)).val, d ⟨j, by omega⟩ = d 0 := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      let a : Fin (n + 1) := ⟨j, by omega⟩
      let b : Fin (n + 1) := ⟨j + 1, by omega⟩
      have ha : a ≤ w.symm (Fin.last n) := Nat.le_of_succ_le hj
      have hb : b ≤ w.symm (Fin.last n) := hj
      have hwa := firstBlock w h ha
      have hwb := firstBlock w h hb
      have hab : a < b := Nat.lt_succ_self _
      have hw : w a < w b := Fin.lt_def.mpr (by dsimp [a, b] at *; omega)
      exact ((h a b hab hw).2 rfl).symm.trans (ih (Nat.le_of_succ_le hj))
  exact aux i.val hi

variable (n : ℕ) (b : Fin (n + 1))

private def splitColumns : Fin (n + 1 - b.val) ⊕ Fin b.val ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

private def splitRows : Fin b.val ⊕ Fin (n + 1 - b.val) ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] private theorem col_left (i : Fin (n + 1 - b.val)) :
    (splitColumns n b (Sum.inl i)).val = i.val := by
  simp [splitColumns, finSumFinEquiv_apply_left]

@[simp] private theorem col_right (i : Fin b.val) :
    (splitColumns n b (Sum.inr i)).val = n + 1 - b.val + i.val := by
  simp [splitColumns, finSumFinEquiv_apply_right]

@[simp] private theorem row_left (i : Fin b.val) :
    (splitRows n b (Sum.inl i)).val = i.val := by
  simp [splitRows, finSumFinEquiv_apply_left]

@[simp] private theorem row_right (i : Fin (n + 1 - b.val)) :
    (splitRows n b (Sum.inr i)).val = b.val + i.val := by
  simp [splitRows, finSumFinEquiv_apply_right]

private def appendPerm (v : Equiv.Perm (Fin b.val)) : Equiv.Perm (Fin (n + 1)) :=
  (splitColumns n b).symm.trans ((Equiv.sumComm _ _).trans
    ((Equiv.sumCongr v (Equiv.refl _)).trans (splitRows n b)))

@[simp] private theorem appendPerm_left (v : Equiv.Perm (Fin b.val)) (i : Fin (n + 1 - b.val)) :
    (appendPerm n b v (splitColumns n b (Sum.inl i))).val = b.val + i.val := by
  simp [appendPerm]

@[simp] private theorem appendPerm_right (v : Equiv.Perm (Fin b.val)) (i : Fin b.val) :
    (appendPerm n b v (splitColumns n b (Sum.inr i))).val = (v i).val := by
  simp [appendPerm]

private def appendLabels (a : α) (d : Fin b.val → α) : Fin (n + 1) → α :=
  fun i => Sum.elim (fun _ => a) d ((splitColumns n b).symm i)

@[simp] private theorem appendLabels_left (a : α) (d : Fin b.val → α) (i : Fin (n + 1 - b.val)) :
    appendLabels n b a d (splitColumns n b (Sum.inl i)) = a := by
  simp [appendLabels]

@[simp] private theorem appendLabels_right (a : α) (d : Fin b.val → α) (i : Fin b.val) :
    appendLabels n b a d (splitColumns n b (Sum.inr i)) = d i := by
  simp [appendLabels]

private theorem appendPattern (a : α) {v : Equiv.Perm (Fin b.val)} {d : Fin b.val → α}
    (h : IsMonomialPattern v d) : IsMonomialPattern (appendPerm n b v) (appendLabels n b a d) := by
  intro i j hij hw
  obtain ⟨i, rfl⟩ := (splitColumns n b).surjective i
  obtain ⟨j, rfl⟩ := (splitColumns n b).surjective j
  cases i <;> cases j <;> simp only [Fin.lt_def, col_left, col_right, appendPerm_left,
    appendPerm_right, appendLabels_left, appendLabels_right] at *
  · exact ⟨by omega, fun _ => trivial⟩
  · omega
  · omega
  · obtain ⟨he, hlabel⟩ := h _ _ (Fin.lt_def.mpr (by omega)) (Fin.lt_def.mpr hw)
    exact ⟨by omega, fun ha => hlabel (by omega)⟩

private def append (x : Σ b : Fin (n + 1), α × MonomialPattern b.val α) : MonomialPattern (n + 1) α :=
  ⟨(appendPerm n x.1 x.2.2.1.1, appendLabels n x.1 x.2.1 x.2.2.1.2),
    appendPattern n x.1 x.2.1 x.2.2.2⟩

private theorem appendPerm_last_preimage (v : Equiv.Perm (Fin b.val)) :
    ((appendPerm n b v).symm (Fin.last n)).val = n - b.val := by
  let i : Fin (n + 1 - b.val) := ⟨n - b.val, by omega⟩
  have hi : appendPerm n b v (splitColumns n b (Sum.inl i)) = Fin.last n := by
    apply Fin.ext
    simp only [appendPerm_left, Fin.val_last, i]
    omega
  rw [← hi, Equiv.symm_apply_apply, col_left]

private theorem append_injective : Function.Injective (append n (α := α)) := by
  rintro ⟨b, a, P⟩ ⟨b', a', P'⟩ h
  have hw : appendPerm n b P.1.1 = appendPerm n b' P'.1.1 :=
    congrArg (fun p : MonomialPattern (n + 1) α => p.1.1) h
  have hsize := congrArg (fun w : Equiv.Perm (Fin (n + 1)) => (w.symm (Fin.last n)).val) hw
  rw [appendPerm_last_preimage, appendPerm_last_preimage] at hsize
  have hb : b = b' := Fin.ext (by omega)
  subst b'
  have hd : appendLabels n b a P.1.2 = appendLabels n b a' P'.1.2 :=
    congrArg (fun p : MonomialPattern (n + 1) α => p.1.2) h
  have ha := congrFun hd (splitColumns n b (Sum.inl ⟨0, by omega⟩))
  rw [appendLabels_left, appendLabels_left] at ha
  have hp : P = P' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Equiv.ext
      intro i
      have hi := congrArg (fun w : Equiv.Perm (Fin (n + 1)) => (w (splitColumns n b (Sum.inr i))).val) hw
      rw [appendPerm_right, appendPerm_right] at hi
      exact Fin.ext hi
    · funext i
      have hi := congrFun hd (splitColumns n b (Sum.inr i))
      simpa only [appendLabels_right] using hi
  rw [ha, hp]

private theorem append_surjective : Function.Surjective (append n (α := α)) := by
  rintro ⟨⟨w, d⟩, h⟩
  let p := w.symm (Fin.last n)
  let b : Fin (n + 1) := ⟨n - p.val, by omega⟩
  have hp : (n + 1 - b.val) = p.val + 1 := by dsimp [b]; omega
  have hleft (i : Fin (n + 1 - b.val)) : (w (splitColumns n b (Sum.inl i))).val = b.val + i.val := by
    have hi : splitColumns n b (Sum.inl i) ≤ p := by
      rw [Fin.le_def, col_left]
      omega
    have hs := firstBlock w h hi
    change (w (splitColumns n b (Sum.inl i))).val + p.val = n + (splitColumns n b (Sum.inl i)).val at hs
    rw [col_left] at hs
    have hb : b.val = n - p.val := rfl
    omega
  have hright (i : Fin b.val) : (w (splitColumns n b (Sum.inr i))).val < b.val := by
    by_contra! hi
    let j : Fin (n + 1 - b.val) := ⟨(w (splitColumns n b (Sum.inr i))).val - b.val, by omega⟩
    have he : w (splitColumns n b (Sum.inl j)) = w (splitColumns n b (Sum.inr i)) := by
      apply Fin.ext
      rw [hleft]
      dsimp [j]
      omega
    have hbad := (splitColumns n b).injective (w.injective he)
    cases hbad
  let vfun (i : Fin b.val) : Fin b.val := ⟨(w (splitColumns n b (Sum.inr i))).val, hright i⟩
  have hinj : Function.Injective vfun := by
    intro i j hij
    have hv : w (splitColumns n b (Sum.inr i)) = w (splitColumns n b (Sum.inr j)) :=
      Fin.ext (congrArg (fun x : Fin b.val => x.val) hij)
    exact Sum.inr.inj ((splitColumns n b).injective (w.injective hv))
  let v := Equiv.ofBijective vfun ⟨hinj, Finite.surjective_of_injective hinj⟩
  let e := fun i : Fin b.val => d (splitColumns n b (Sum.inr i))
  have he : IsMonomialPattern v e := by
    intro i j hij hij'
    have h1 : splitColumns n b (Sum.inr i) < splitColumns n b (Sum.inr j) := by
      simpa only [Fin.lt_def, col_right, Nat.add_lt_add_iff_left] using hij
    have h2 : w (splitColumns n b (Sum.inr i)) < w (splitColumns n b (Sum.inr j)) := hij'
    have h' := h _ _ h1 h2
    simp only [col_right] at h'
    refine ⟨?_, fun ha => h'.2 (by omega)⟩
    change (i.val + 1 = j.val) ↔
      (w (splitColumns n b (Sum.inr i))).val + 1 = (w (splitColumns n b (Sum.inr j))).val
    omega
  refine ⟨⟨b, d 0, ⟨(v, e), he⟩⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
  · apply Equiv.ext
    intro i
    change appendPerm n b v i = w i
    obtain ⟨i, rfl⟩ := (splitColumns n b).surjective i
    cases i with
    | inl i => apply Fin.ext; rw [appendPerm_left, hleft]
    | inr i => apply Fin.ext; rw [appendPerm_right]; rfl
  · funext i
    change appendLabels n b (d 0) e i = d i
    obtain ⟨i, rfl⟩ := (splitColumns n b).surjective i
    cases i with
    | inl i =>
      rw [appendLabels_left]
      symm
      apply firstBlock_labels w h
      rw [Fin.le_def, col_left]
      omega
    | inr i => rw [appendLabels_right]

/-- A positive-rank pattern splits into a constant labelled initial block and a smaller pattern. -/
def firstBlockEquiv : MonomialPattern (n + 1) α ≃ Σ b : Fin (n + 1), α × MonomialPattern b.val α :=
  (Equiv.ofBijective (append n) ⟨append_injective n, append_surjective n⟩).symm

private theorem card_zero : Nat.card (MonomialPattern 0 α) = 1 := by
  let : Unique (MonomialPattern 0 α) :=
    { default := ⟨(Equiv.refl _, Fin.elim0), fun i => Fin.elim0 i⟩
      uniq := fun p => Subtype.ext (Prod.ext (Equiv.ext fun i => Fin.elim0 i) (funext fun i => Fin.elim0 i)) }
  exact Nat.card_unique

private theorem card_succ_rec [Finite α] (n : ℕ) :
    Nat.card (MonomialPattern (n + 1) α) = Nat.card α * ∑ b : Fin (n + 1), Nat.card (MonomialPattern b.val α) := by
  rw [Nat.card_congr (firstBlockEquiv n), Nat.card_sigma, Finset.mul_sum]
  simp_rw [Nat.card_prod]

/-- In rank `n+1`, there is an initial label and then `n` independent choices of continuing a
block or starting one with any label. -/
theorem card_succ [Finite α] (n : ℕ) :
    Nat.card (MonomialPattern (n + 1) α) = Nat.card α * (Nat.card α + 1) ^ n := by
  induction n with
  | zero =>
    rw [card_succ_rec, Fin.sum_univ_one, Fin.val_zero, card_zero]
    simp
  | succ n ih =>
    rw [card_succ_rec (α := α) (n + 1), Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, mul_add]
    rw [← card_succ_rec (α := α) n, ih, pow_succ]
    ring

end MonomialPattern

end Langlands.GeneralLinear
