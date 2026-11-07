import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.Data.Nat.Find

/-! # Simple reflection words enumerating the positive roots -/

noncomputable section

open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u v w

namespace Langlands.PositiveRootWord

variable {J : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (b : P.Base)
    [Fintype J] [P.IsReduced]

/-- Positive roots sent negative by the inverse of an actual root-datum
automorphism. -/
def inversionRoots (w : P.Aut) : Finset J := by
  classical
  exact Finset.univ.filter fun j => b.IsPos j ∧ ¬ b.IsPos (w.indexEquiv.symm j)

omit [P.IsReduced] in
@[simp] theorem mem_inversionRoots (w : P.Aut) (j : J) :
    j ∈ inversionRoots P b w ↔ b.IsPos j ∧ ¬ b.IsPos (w.indexEquiv.symm j) := by
  classical
  simp [inversionRoots]

omit [Fintype J] [P.IsReduced] in
private theorem height_image_negative (w : P.Aut) (i : J) :
    b.height (w.indexEquiv (P.reflectionPerm i i)) =
      -b.height (w.indexEquiv i) := by
  have he : w.indexEquiv (P.reflectionPerm i i) =
    P.reflectionPerm (w.indexEquiv i) (w.indexEquiv i) := by
    apply P.root.injective
    calc
      P.root (w.indexEquiv (P.reflectionPerm i i)) = -(w • P.root i) := by
        rw [RootPairing.Equiv.root_indexEquiv_eq_smul,
          RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, smul_neg]
      _ = -P.root (w.indexEquiv i) := by
        rw [RootPairing.Equiv.root_indexEquiv_eq_smul]
      _ = P.root (P.reflectionPerm (w.indexEquiv i) (w.indexEquiv i)) := by
        rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  rw [he]
  exact b.height_reflectionPerm_self _

/-- A right simple reflection whose current root is positive adds precisely
that root to the inversion set. -/
theorem inversionRoots_mul_simple (w : P.Aut) (i : b.support)
    (hi : b.IsPos (w.indexEquiv i)) :
    inversionRoots P b (w * RootPairing.Equiv.reflection P i) =
      insert (w.indexEquiv i) (inversionRoots P b w) := by
  classical
  ext j
  have hsymm : (w * RootPairing.Equiv.reflection P i).indexEquiv.symm j =
      P.reflectionPerm i (w.indexEquiv.symm j) := by
    have hmul : (w * RootPairing.Equiv.reflection P i).indexEquiv =
        w.indexEquiv * P.reflectionPerm i :=
      (RootPairing.Equiv.indexHom P).map_mul w (RootPairing.Equiv.reflection P i)
    apply (w * RootPairing.Equiv.reflection P i).indexEquiv.injective
    rw [Equiv.apply_symm_apply, hmul]
    simp only [Equiv.Perm.mul_apply, P.reflectionPerm_self, Equiv.apply_symm_apply]
  simp only [mem_inversionRoots, Finset.mem_insert, hsymm]
  by_cases hj : j = w.indexEquiv i
  · subst j
    simp only [Equiv.symm_apply_apply]
    have hn : ¬ b.IsPos (P.reflectionPerm i i) := by
      have hh : b.height (P.reflectionPerm i i) = -b.height i :=
        b.height_reflectionPerm_self i
      rw [RootPairing.Base.isPos_iff, hh,
        b.height_one_of_mem_support i.property]
      omega
    exact iff_of_true ⟨hi, hn⟩ (Or.inl trivial)
  · have hz : w.indexEquiv.symm j ≠ (i : J) := by
      intro he
      exact hj ((w.indexEquiv.apply_symm_apply j).symm.trans
        (congrArg w.indexEquiv he))
    by_cases hpj : b.IsPos j
    · have hsz : P.reflectionPerm i (w.indexEquiv.symm j) ≠ (i : J) := by
        intro he
        have he' : w.indexEquiv.symm j = P.reflectionPerm i i := by
          have h := congrArg (P.reflectionPerm i) he
          rwa [P.reflectionPerm_self] at h
        have hj' : j = w.indexEquiv (P.reflectionPerm i i) :=
          (w.indexEquiv.apply_symm_apply j).symm.trans (congrArg w.indexEquiv he')
        have hn := height_image_negative P b w i
        rw [← hj'] at hn
        rw [RootPairing.Base.isPos_iff] at hpj hi
        omega
      have hiff : b.IsPos (P.reflectionPerm i (w.indexEquiv.symm j)) ↔
          b.IsPos (w.indexEquiv.symm j) := by
        constructor
        · intro h
          simpa only [P.reflectionPerm_self] using h.reflectionPerm i.property hsz
        · intro h
          exact h.reflectionPerm i.property hz
      simp only [hpj, true_and, hj, false_or, hiff]
    · simp only [hpj, false_and, hj, false_or]

omit [P.IsReduced] in
/-- If all simple roots have negative images, all positive roots have negative
images. -/
theorem not_isPos_image_of_simple (w : P.Aut)
    (hw : ∀ i : b.support, ¬ b.IsPos (w.indexEquiv i))
    {j : J} (hj : b.IsPos j) : ¬ b.IsPos (w.indexEquiv j) := by
  apply hj.induction_on_add
  · intro i hi
    exact hw ⟨i, hi⟩
  · intro i j k hk hi hj
    have hj' := hw ⟨j, hj⟩
    have he : P.root (w.indexEquiv k) =
        P.root (w.indexEquiv i) + P.root (w.indexEquiv j) := by
      simp only [RootPairing.Equiv.root_indexEquiv_eq_smul, ← smul_add, hk]
    have hh := b.height_add he
    simp only [RootPairing.Base.isPos_iff] at hi hj' ⊢
    omega

/-- A list is read from its tail: a new head multiplies the previous
automorphism on the right. -/
def wordAut : List b.support → P.Aut
  | [] => 1
  | i :: l => wordAut l * RootPairing.Equiv.reflection P i

/-- The root at a new head is the image of its simple root under the previous
automorphism. The resulting list is in reverse chronological order. -/
def wordRoots : List b.support → List J
  | [] => []
  | i :: l => (wordAut P b l).indexEquiv i :: wordRoots l

/-- Every successive root of the word is positive. -/
def IsPositive (l : List b.support) : Prop :=
  ∀ j ∈ wordRoots P b l, b.IsPos j

omit [Fintype J] [P.IsReduced] in
@[simp] theorem isPositive_nil : IsPositive P b [] := by
  simp [IsPositive, wordRoots]

omit [Fintype J] [P.IsReduced] in
@[simp] theorem isPositive_cons (i : b.support) (l : List b.support) :
    IsPositive P b (i :: l) ↔
      b.IsPos ((wordAut P b l).indexEquiv i) ∧ IsPositive P b l := by
  simp [IsPositive, wordRoots]

omit [Fintype J] [P.IsReduced] in
@[simp] theorem length_wordRoots (l : List b.support) :
    (wordRoots P b l).length = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [wordRoots, ih]

/-- Positivity makes the roots distinct and identifies their set with the
inversion set of the word automorphism. -/
theorem wordRoots_nodup_toFinset (l : List b.support) (hl : IsPositive P b l) :
    (wordRoots P b l).Nodup ∧
      (wordRoots P b l).toFinset = inversionRoots P b (wordAut P b l) := by
  induction l with
  | nil => simp [wordRoots, wordAut, inversionRoots]
  | cons i l ih =>
    rcases (isPositive_cons P b i l).mp hl with ⟨hi, hl⟩
    rcases ih hl with ⟨hn, he⟩
    have hnot : (wordAut P b l).indexEquiv i ∉
        inversionRoots P b (wordAut P b l) := by
      simp only [mem_inversionRoots, Equiv.symm_apply_apply, not_and, not_not]
      intro _
      exact b.isPos_of_mem_support i.property
    constructor
    · rw [wordRoots, List.nodup_cons]
      exact ⟨fun h => hnot (he ▸ List.mem_toFinset.mpr h), hn⟩
    · rw [wordRoots, List.toFinset_cons, he, wordAut,
        inversionRoots_mul_simple P b _ i hi]

/-- The length of a positive word is bounded by the number of positive roots. -/
theorem length_le_card_positiveRoots (l : List b.support) (hl : IsPositive P b l) :
    l.length ≤ (Finset.univ.filter b.IsPos).card := by
  rcases wordRoots_nodup_toFinset P b l hl with ⟨hn, he⟩
  calc
    l.length = (wordRoots P b l).toFinset.card := by
      rw [List.toFinset_card_of_nodup hn, length_wordRoots]
    _ ≤ (Finset.univ.filter b.IsPos).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hl j (List.mem_toFinset.mp hj)

/-- There is a positive simple-reflection word whose successive roots list
every positive root exactly once and whose automorphism sends all positive
roots to negative roots. -/
theorem exists_positive_word :
    ∃ l : List b.support, IsPositive P b l ∧ (wordRoots P b l).Nodup ∧
      (∀ j : J, j ∈ wordRoots P b l ↔ b.IsPos j) ∧
      (∀ j : J, b.IsPos j → ¬ b.IsPos ((wordAut P b l).indexEquiv j)) := by
  classical
  let Q : ℕ → Prop := fun n => ∃ l : List b.support, l.length = n ∧ IsPositive P b l
  let N := (Finset.univ.filter b.IsPos).card
  have hzero : Q 0 := ⟨[], rfl, isPositive_nil P b⟩
  obtain ⟨l, hlen, hl⟩ := Nat.findGreatest_spec (Nat.zero_le N) hzero
  have hsimple : ∀ i : b.support, ¬ b.IsPos ((wordAut P b l).indexEquiv i) := by
    intro i hi
    have hcons : IsPositive P b (i :: l) := (isPositive_cons P b i l).mpr ⟨hi, hl⟩
    have hbound := length_le_card_positiveRoots P b (i :: l) hcons
    have hmax := Nat.le_findGreatest hbound
      (show Q (i :: l).length from ⟨i :: l, rfl, hcons⟩)
    change l.length + 1 ≤ Nat.findGreatest Q N at hmax
    omega
  have hall : ∀ j : J, b.IsPos j → ¬ b.IsPos ((wordAut P b l).indexEquiv j) :=
    fun _ hj => not_isPos_image_of_simple P b _ hsimple hj
  rcases wordRoots_nodup_toFinset P b l hl with ⟨hn, he⟩
  refine ⟨l, hl, hn, ?_, hall⟩
  intro j
  constructor
  · exact hl j
  · intro hj
    apply List.mem_toFinset.mp
    rw [he, mem_inversionRoots]
    refine ⟨hj, ?_⟩
    intro hpre
    exact hall _ hpre (by simpa only [Equiv.apply_symm_apply] using hj)

end Langlands.PositiveRootWord
