import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

/-! # Multisets of a prescribed additive weight -/

noncomputable section

namespace Langlands

/-- Multisets whose labels have total weight `n`. -/
abbrev WeightedMultiset {α : Type*} (w : α → ℕ) (n : ℕ) :=
  {s : Multiset α // (s.map w).sum = n}

namespace WeightedMultiset

variable {α β : Type*} {w : α → ℕ} {v : β → ℕ} {n : ℕ}

/-- A weight-preserving equivalence of labels relabels multisets of fixed total weight. -/
def congr (e : α ≃ β) (he : ∀ a, v (e a) = w a) : WeightedMultiset w n ≃ WeightedMultiset v n where
  toFun s := ⟨s.val.map e, by rw [Multiset.map_map]; simpa only [Function.comp_def, he] using s.2⟩
  invFun s := ⟨s.val.map e.symm, by
    have he' (b : β) : w (e.symm b) = v b := by rw [← he, e.apply_symm_apply]
    rw [Multiset.map_map]
    simpa only [Function.comp_def, he'] using s.2⟩
  left_inv s := Subtype.ext (by simp [Multiset.map_map])
  right_inv s := Subtype.ext (by simp [Multiset.map_map])

/-- A singleton is a weighted multiset at the weight of its label. -/
def singleton (a : {a : α // w a = n}) : WeightedMultiset w n :=
  ⟨{a.val}, by simpa using a.2⟩

private theorem singleton_injective : Function.Injective (singleton (w := w) (n := n)) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  exact Multiset.singleton_inj.mp h'

private abbrev LowerLabel (w : α → ℕ) (n : ℕ) := {a : α // w a < n}

private def includeLower (s : WeightedMultiset (fun a : LowerLabel w n => w a.val) n) :
    WeightedMultiset w n :=
  ⟨s.val.map Subtype.val, by simpa only [Multiset.map_map, Function.comp_def] using s.2⟩

private theorem includeLower_injective : Function.Injective (includeLower (w := w) (n := n)) := fun _ _ h =>
  Subtype.ext (Multiset.map_injective Subtype.val_injective (congrArg Subtype.val h))

private theorem sum_ne_zero_of_pos (hp : ∀ a, 0 < w a) (s : Multiset α) (hs : s ≠ 0) :
    (s.map w).sum ≠ 0 := by
  induction s using Multiset.induction with
  | empty => exact (hs rfl).elim
  | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons]; have := hp a; omega

private theorem lowerOrSingleton (hp : ∀ a, 0 < w a) (s : WeightedMultiset w n) :
    (∃ a : {a : α // w a = n}, singleton a = s) ∨
      ∀ a ∈ s.val, w a < n := by
  classical
  by_cases h : ∃ a ∈ s.val, w a = n
  · left
    obtain ⟨a, ha, hwa⟩ := h
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
    have he := s.2
    rw [ht, Multiset.map_cons, Multiset.sum_cons, hwa] at he
    have ht0 : t = 0 := by by_contra h'; exact sum_ne_zero_of_pos hp t h' (by omega)
    exact ⟨⟨a, hwa⟩, Subtype.ext (by simpa [singleton, ht0] using ht.symm)⟩
  · right
    intro a ha
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
    have he := s.2
    rw [ht, Multiset.map_cons, Multiset.sum_cons] at he
    have hne : w a ≠ n := fun e => h ⟨a, ha, e⟩
    omega

/-- A multiset of total weight `n` is either a singleton of weight `n` or a multiset
of labels of strictly smaller weights, provided every label has positive weight. -/
def singletonOrLower (hp : ∀ a, 0 < w a) :
    ({a : α // w a = n} ⊕ WeightedMultiset (fun a : {a : α // w a < n} => w a.val) n) ≃
      WeightedMultiset w n := by
  refine Equiv.ofBijective (Sum.elim singleton includeLower) ⟨?_, ?_⟩
  · intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (singleton_injective h)
      | inr b =>
        have h' : a.val ∈ b.val.map Subtype.val := by
          rw [← show ({a.val} : Multiset α) = b.val.map Subtype.val from congrArg Subtype.val h]
          exact Multiset.mem_singleton_self _
        obtain ⟨c, _, hc⟩ := Multiset.mem_map.mp h'
        exact (c.2.ne (hc ▸ a.2)).elim
    | inr a =>
      cases y with
      | inr b => exact congrArg Sum.inr (includeLower_injective h)
      | inl b =>
        have h' : b.val ∈ a.val.map Subtype.val := by
          rw [show a.val.map Subtype.val = ({b.val} : Multiset α) from congrArg Subtype.val h]
          exact Multiset.mem_singleton_self _
        obtain ⟨c, _, hc⟩ := Multiset.mem_map.mp h'
        exact (c.2.ne (hc ▸ b.2)).elim
  · intro s
    rcases lowerOrSingleton hp s with ⟨a, ha⟩ | h
    · exact ⟨Sum.inl a, ha⟩
    · let m := s.val.attach.map (fun a => (⟨a.val, h _ a.2⟩ : LowerLabel w n))
      have hm : m.map Subtype.val = s.val := by simp [m, Multiset.map_map]
      have hs : (m.map fun a => w a.val).sum = n := by
        rw [show m.map (fun a => w a.val) = (m.map Subtype.val).map w from (Multiset.map_map _ _ _).symm, hm]
        exact s.2
      exact ⟨Sum.inr ⟨m, hs⟩, Subtype.ext hm⟩

private def lowerFiberEquiv (w : α → ℕ) (n : ℕ) :
    LowerLabel w n ≃ Σ d : Fin n, {a : α // w a = d.val} where
  toFun a := ⟨⟨w a.val, a.2⟩, ⟨a.val, rfl⟩⟩
  invFun a := ⟨a.2.val, by rw [a.2.property]; exact a.1.isLt⟩
  left_inv a := Subtype.ext rfl
  right_inv := by
    rintro ⟨⟨d, hd⟩, ⟨a, ha⟩⟩
    change w a = d at ha
    subst d
    rfl

/-- Finite weighted-multiset counts in every rank determine the number of labels of each weight. -/
theorem card_fiber_eq_of_card_eq (hp : ∀ a, 0 < w a) (hq : ∀ b, 0 < v b)
    (hf : ∀ n, Finite (WeightedMultiset w n)) (hg : ∀ n, Finite (WeightedMultiset v n))
    (h : ∀ n, Nat.card (WeightedMultiset w n) = Nat.card (WeightedMultiset v n)) (n : ℕ) :
    Nat.card {a : α // w a = n} = Nat.card {b : β // v b = n} := by
  classical
  have fα (d : ℕ) : Finite {a : α // w a = d} := by
    let := hf d
    exact Finite.of_injective singleton singleton_injective
  have fβ (d : ℕ) : Finite {b : β // v b = d} := by
    let := hg d
    exact Finite.of_injective singleton singleton_injective
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let fiber (d : Fin n) : {a : α // w a = d.val} ≃ {b : β // v b = d.val} := by
      let := fα d.val
      let := fβ d.val
      let := Fintype.ofFinite {a : α // w a = d.val}
      let := Fintype.ofFinite {b : β // v b = d.val}
      exact Fintype.equivOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using ih d.val d.isLt)
    let e : LowerLabel w n ≃ LowerLabel v n :=
      (lowerFiberEquiv w n).trans ((Equiv.sigmaCongrRight fiber).trans (lowerFiberEquiv v n).symm)
    have hweight (a : LowerLabel w n) : v (e a).val = w a.val :=
      (fiber ⟨w a.val, a.2⟩ ⟨a.val, rfl⟩).2
    have ht := Nat.card_congr
      (congr (w := fun a : LowerLabel w n => w a.val)
        (v := fun b : LowerLabel v n => v b.val) (n := n) e hweight)
    let := hf n
    let := hg n
    let := fα n
    let := fβ n
    let : Finite (WeightedMultiset (fun a : LowerLabel w n => w a.val) n) :=
      Finite.of_injective includeLower includeLower_injective
    let : Finite (WeightedMultiset (fun b : LowerLabel v n => v b.val) n) :=
      Finite.of_injective includeLower includeLower_injective
    have he := h n
    rw [← Nat.card_congr (singletonOrLower (n := n) hp),
      ← Nat.card_congr (singletonOrLower (n := n) hq), Nat.card_sum, Nat.card_sum, ht] at he
    exact Nat.add_right_cancel he

end WeightedMultiset

end Langlands
