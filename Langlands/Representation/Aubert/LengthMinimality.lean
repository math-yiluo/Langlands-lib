import Langlands.Representation.Geometric.PermutationDescents
import Langlands.Representation.Geometric.BlockWeylCutProof
import Langlands.Representation.Aubert.TwoSidedSupport

/-! Inversion length and actual minimum representatives of block Weyl double cosets. -/

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

variable {n : ℕ}

/-- The positive pairs reversed by an actual coordinate permutation. -/
def inversions (w : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ w p.2 < w p.1

@[simp] theorem mem_inversions (w : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ inversions w ↔ p.1 < p.2 ∧ w p.2 < w p.1 := by
  simp [inversions]

/-- The inversion count used as the length rank on the actual symmetric group. -/
def inversionLength (w : Equiv.Perm (Fin n)) : ℕ := (inversions w).card

theorem inversionLength_symm (w : Equiv.Perm (Fin n)) :
    inversionLength w.symm = inversionLength w := by
  symm
  apply Finset.card_bij (fun p _ => (w p.2, w p.1))
  · intro p hp
    simpa only [mem_inversions, Equiv.symm_apply_apply] using
      (And.symm ((mem_inversions w p).mp hp))
  · intro p hp q hq heq
    have h1 := w.injective (congrArg Prod.snd heq)
    have h2 := w.injective (congrArg Prod.fst heq)
    exact Prod.ext h1 h2
  · intro p hp
    refine ⟨(w.symm p.2, w.symm p.1), ?_, ?_⟩
    · simpa only [mem_inversions, Equiv.apply_symm_apply] using
        (And.symm ((mem_inversions w.symm p).mp hp))
    · simp

private theorem swap_lt_iff_of_not_pair {a b x y : Fin n}
    (hab : a.val + 1 = b.val) (hxy : (x, y) ≠ (a, b)) (hyx : (x, y) ≠ (b, a)) :
    Equiv.swap a b x < Equiv.swap a b y ↔ x < y := by
  have h1 : ¬ (x = a ∧ y = b) := fun h => hxy (Prod.ext h.1 h.2)
  have h2 : ¬ (x = b ∧ y = a) := fun h => hyx (Prod.ext h.1 h.2)
  simp only [Equiv.swap_apply_def]
  split_ifs <;>
    simp_all only [Fin.ext_iff, Fin.lt_def, and_self, not_true_eq_false] <;> omega

private theorem inversion_swap_iff (w : Equiv.Perm (Fin n)) {a b : Fin n}
    (hab : a.val + 1 = b.val) (hw : w b < w a) (p : Fin n × Fin n) :
    p ∈ inversions (w * Equiv.swap a b) ↔
      (Equiv.swap a b p.1, Equiv.swap a b p.2) ∈ (inversions w).erase (a, b) := by
  have hne : a ≠ b := by intro h; have := congrArg Fin.val h; omega
  by_cases hp : p = (a, b)
  · subst p
    simp [hne, not_lt_of_gt hw]
  by_cases hp' : p = (b, a)
  · subst p
    have hba : ¬ b < a := by change ¬ b.val < a.val; omega
    simp [hba]
  have horder := swap_lt_iff_of_not_pair hab hp hp'
  have hnot : (Equiv.swap a b p.1, Equiv.swap a b p.2) ≠ (a, b) := by
    intro heq
    apply hp'
    apply Prod.ext
    · have h := congrArg (Equiv.swap a b) (congrArg Prod.fst heq)
      simpa only [Equiv.swap_apply_self, Equiv.swap_apply_left] using h
    · have h := congrArg (Equiv.swap a b) (congrArg Prod.snd heq)
      simpa only [Equiv.swap_apply_self, Equiv.swap_apply_right] using h
  simp only [mem_inversions, Equiv.Perm.mul_apply, Finset.mem_erase, horder]
  exact ⟨fun h => ⟨hnot, h⟩, fun h => h.2⟩

/-- An adjacent descent lowers the inversion count by precisely one. -/
theorem inversionLength_mul_swap_add_one (w : Equiv.Perm (Fin n)) {a b : Fin n}
    (hab : a.val + 1 = b.val) (hw : w b < w a) :
    inversionLength (w * Equiv.swap a b) + 1 = inversionLength w := by
  have hcard : (inversions (w * Equiv.swap a b)).card =
      ((inversions w).erase (a, b)).card := by
    apply Finset.card_bij (fun p _ => (Equiv.swap a b p.1, Equiv.swap a b p.2))
    · intro p hp
      exact (inversion_swap_iff w hab hw p).mp hp
    · intro p hp q hq heq
      exact Prod.ext ((Equiv.swap a b).injective (congrArg Prod.fst heq))
        ((Equiv.swap a b).injective (congrArg Prod.snd heq))
    · intro p hp
      refine ⟨(Equiv.swap a b p.1, Equiv.swap a b p.2), ?_, ?_⟩
      · apply (inversion_swap_iff w hab hw _).mpr
        simpa only [Equiv.swap_apply_self] using hp
      · simp
  change (inversions (w * Equiv.swap a b)).card + 1 = (inversions w).card
  rw [hcard]
  apply Finset.card_erase_add_one
  exact (mem_inversions w (a, b)).mpr ⟨by change a.val < b.val; omega, hw⟩

/-- Adjacent inverse descents give the corresponding left-multiplication formula. -/
theorem inversionLength_swap_mul_add_one (w : Equiv.Perm (Fin n)) {a b : Fin n}
    (hab : a.val + 1 = b.val) (hw : w.symm b < w.symm a) :
    inversionLength (Equiv.swap a b * w) + 1 = inversionLength w := by
  rw [← inversionLength_symm (Equiv.swap a b * w)]
  have hinv : (Equiv.swap a b * w).symm = w.symm * Equiv.swap a b := by
    simp [← Equiv.Perm.inv_def]
  rw [hinv, inversionLength_mul_swap_add_one w.symm hab hw, inversionLength_symm]

/-- Swapping two coordinates of one block is an element of its actual Weyl subgroup. -/
theorem swap_mem_blockWeyl (B : BlockShape n) {a b : Fin n}
    (hab : blockIndex B a = blockIndex B b) :
    Equiv.swap a b ∈ blockWeyl B := by
  intro x
  simp only [Equiv.swap_apply_def]
  split_ifs with hx hx
  · simpa only [hx] using hab.symm
  · simpa only [hx] using hab
  · rfl

/-- A minimum-inversion element of a block Weyl double coset satisfies the
actual increasing-block conditions in both directions. -/
theorem isMinimalRepresentative_of_minimum_inversionLength
    (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (hmin : ∀ v ∈ DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B),
      inversionLength w ≤ inversionLength v) :
    IsMinimalRepresentative B C w := by
  rw [isMinimalRepresentative_iff_descents]
  constructor
  · intro i hi heq
    let a : Fin n := ⟨i.val, by omega⟩
    let b : Fin n := ⟨i.val + 1, by omega⟩
    have hs : Equiv.swap a b ∈ blockWeyl B := swap_mem_blockWeyl B heq
    have hcos : w * Equiv.swap a b ∈
        DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B) := by
      exact DoubleCoset.mem_doubleCoset.mpr
        ⟨1, (blockWeyl C).one_mem, Equiv.swap a b, hs, by simp⟩
    have hle := hmin _ hcos
    have hlen := inversionLength_mul_swap_add_one w (a := a) (b := b) rfl
      ((mem_permutationDescents w i).mp hi)
    omega
  · intro i hi heq
    let a : Fin n := ⟨i.val, by omega⟩
    let b : Fin n := ⟨i.val + 1, by omega⟩
    have hs : Equiv.swap a b ∈ blockWeyl C := swap_mem_blockWeyl C heq
    have hcos : Equiv.swap a b * w ∈
        DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B) := by
      exact DoubleCoset.mem_doubleCoset.mpr
        ⟨Equiv.swap a b, hs, 1, (blockWeyl B).one_mem, by simp⟩
    have hle := hmin _ hcos
    have hlen := inversionLength_swap_mul_add_one w (a := a) (b := b) rfl
      ((mem_permutationDescents w.symm i).mp hi)
    omega

theorem exists_minimum_inversionLength (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    ∃ v ∈ DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B),
      ∀ x ∈ DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B),
        inversionLength v ≤ inversionLength x := by
  classical
  have hex : ∃ k, ∃ v ∈ DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B),
      inversionLength v = k :=
    ⟨inversionLength w, w, DoubleCoset.mem_doubleCoset_self _ _ _, rfl⟩
  obtain ⟨v, hv, hlen⟩ := Nat.find_spec hex
  refine ⟨v, hv, ?_⟩
  intro x hx
  rw [hlen]
  exact Nat.find_min' hex ⟨x, hx, rfl⟩

private theorem minimal_eq_of_mem_doubleCoset
    (B C : BlockShape n) (w v : Equiv.Perm (Fin n))
    (hw : IsMinimalRepresentative B C w) (hv : IsMinimalRepresentative B C v)
    (hcos : v ∈ DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B)) : v = w := by
  have heq : (⟨v, hv⟩ : MinimalRepresentatives B C) = ⟨w, hw⟩ :=
    weylDoubleCoset_injective B C
      (DoubleCoset.mk_eq_of_doubleCoset_eq (DoubleCoset.doubleCoset_eq_of_mem hcos))
  exact congrArg Subtype.val heq

/-- The increasing-block conditions characterize minimum inversion count. -/
theorem isMinimalRepresentative_iff_minimum_inversionLength
    (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    IsMinimalRepresentative B C w ↔
      ∀ v ∈ DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B),
        inversionLength w ≤ inversionLength v := by
  constructor
  · intro hw
    obtain ⟨v, hv, hmin⟩ := exists_minimum_inversionLength B C w
    have hminv : ∀ x ∈ DoubleCoset.doubleCoset v (blockWeyl C) (blockWeyl B),
        inversionLength v ≤ inversionLength x := by
      simpa only [DoubleCoset.doubleCoset_eq_of_mem hv] using hmin
    have hvmin := isMinimalRepresentative_of_minimum_inversionLength B C v hminv
    have heq := minimal_eq_of_mem_doubleCoset B C w v hw hvmin hv
    simpa only [heq] using hmin
  · exact isMinimalRepresentative_of_minimum_inversionLength B C w

/-- The minimum is strict away from the unique increasing-block representative. -/
theorem inversionLength_lt_of_minimal_of_ne (B C : BlockShape n)
    (w v : Equiv.Perm (Fin n)) (hw : IsMinimalRepresentative B C w)
    (hv : v ∈ DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B)) (hne : v ≠ w) :
    inversionLength w < inversionLength v := by
  have hmin := (isMinimalRepresentative_iff_minimum_inversionLength B C w).mp hw
  have hle := hmin v hv
  by_contra hlt
  have hlen : inversionLength v = inversionLength w := le_antisymm (by omega) hle
  have hminv : ∀ x ∈ DoubleCoset.doubleCoset v (blockWeyl C) (blockWeyl B),
      inversionLength v ≤ inversionLength x := by
    intro x hx
    rw [hlen]
    exact hmin x ((DoubleCoset.doubleCoset_eq_of_mem hv) ▸ hx)
  have hvmin := isMinimalRepresentative_of_minimum_inversionLength B C v hminv
  exact hne (minimal_eq_of_mem_doubleCoset B C w v hw hvmin hv)

/-- The set-theoretic singleton-drop argument now yields the actual root-order
condition when the supplied tail is ordered by inversion length. -/
theorem singleton_drop_isMinimalRepresentative
    (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
    (hTail : ∀ v ∈ θ \ {w}, inversionLength w ≤ inversionLength v)
    (hChange : weylSupport B C θ ≠ weylSupport B C (θ \ {w})) :
    IsMinimalRepresentative B C w :=
  isMinimalRepresentative_of_minimum_inversionLength B C w
    (singleton_drop_forces_minimal (blockWeyl C) (blockWeyl B)
      inversionLength θ w hTail hChange)

/-- On a full length tail, the core changes exactly at its minimum representative. -/
theorem singleton_drop_iff_minimal_of_length_tail
    (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
    (hwθ : w ∈ θ)
    (hTail : ∀ v ∈ θ \ {w}, inversionLength w ≤ inversionLength v)
    (hAbove : ∀ v, inversionLength w < inversionLength v → v ∈ θ) :
    weylSupport B C θ ≠ weylSupport B C (θ \ {w}) ↔
      IsMinimalRepresentative B C w := by
  constructor
  · exact singleton_drop_isMinimalRepresentative B C θ w hTail
  · intro hw
    apply (twoSidedCore_diff_singleton_ne_iff (blockWeyl C) (blockWeyl B) θ w).mpr
    intro v hv
    by_cases heq : v = w
    · exact heq ▸ hwθ
    · exact hAbove v (inversionLength_lt_of_minimal_of_ne B C w v hw hv heq)

theorem adjacent_blockIndex_ne_iff_cut (B : BlockShape n) (i : Fin (n - 1)) :
    blockIndex B (⟨i.val, by omega⟩ : Fin n) ≠
        blockIndex B (⟨i.val + 1, by omega⟩ : Fin n) ↔ i ∈ B.cuts := by
  let a : Fin n := ⟨i.val, by omega⟩
  let b : Fin n := ⟨i.val + 1, by omega⟩
  constructor
  · intro hne
    by_contra hi
    have hs := (adjacent_swap_mem_blockWeyl_iff B i).mpr hi
    have heq := hs a
    rw [Equiv.swap_apply_left] at heq
    exact hne heq.symm
  · intro hi heq
    have hs := swap_mem_blockWeyl B heq
    exact ((adjacent_swap_mem_blockWeyl_iff B i).mp hs) hi

/-- Both root-order conditions are literal cut-subset conditions. -/
theorem isMinimalRepresentative_iff_cut_subsets (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    IsMinimalRepresentative B C w ↔
      permutationDescents w ⊆ B.cuts ∧ permutationDescents w.symm ⊆ C.cuts := by
  rw [isMinimalRepresentative_iff_descents]
  simp only [adjacent_blockIndex_ne_iff_cut, Finset.subset_iff]

end Langlands.Aubert.Support
