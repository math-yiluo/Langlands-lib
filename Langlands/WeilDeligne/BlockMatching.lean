import Langlands.WeilDeligne.BlockStatements
import Mathlib.Data.Fintype.EquivFin

/-! # Finite matching from block multiplicities -/

noncomputable section

namespace Langlands.WeilDeligneRepresentation.Blocks

universe uK uG uV uW uX uι uκ

/-- Equal cardinalities of all common fibers provide an equivalence over the base. -/
theorem exists_equiv_of_fiber_card_eq {ι : Type uι} {κ : Type uκ} {α : Type uX}
    [Fintype ι] [Fintype κ] (f : ι → α) (g : κ → α)
    (h : ∀ a, Nat.card {i // f i = a} = Nat.card {j // g j = a}) :
    ∃ e : ι ≃ κ, ∀ i, f i = g (e i) := by
  classical
  let E (a : α) : {i // f i = a} ≃ {j // g j = a} :=
    Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h a)
  exact ⟨_root_.Equiv.ofFiberEquiv E, fun i => (_root_.Equiv.ofFiberEquiv_map E i).symm⟩

/-- Equal numbers of elements in every equivalence class give a class-preserving matching. -/
theorem exists_equiv_of_setoid_card_eq {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] (s : Setoid (ι ⊕ κ))
    (h : ∀ a, Nat.card {i // s.r (Sum.inl i) a} =
      Nat.card {j // s.r (Sum.inr j) a}) :
    ∃ e : ι ≃ κ, ∀ i, s.r (Sum.inl i) (Sum.inr (e i)) := by
  classical
  let f : ι → Quotient s := fun i => Quotient.mk s (Sum.inl i)
  let g : κ → Quotient s := fun j => Quotient.mk s (Sum.inr j)
  have hc : ∀ a, Nat.card {i // f i = a} = Nat.card {j // g j = a} := by
    intro a
    induction a using Quotient.inductionOn with
    | h a => simpa only [f, g, Quotient.eq] using h a
  obtain ⟨e, he⟩ := exists_equiv_of_fiber_card_eq f g hc
  exact ⟨e, fun i => Quotient.exact (he i)⟩

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- Two block data match when the length and Weil-factor isomorphism class agree. -/
def BlockDataMatch (a : BlockDatum.{uK,uG,uV} K G)
    (b : BlockDatum.{uK,uG,uW} K G) : Prop :=
  a.length = b.length ∧ Nonempty (FiniteRepresentation.Equiv a.representation b.representation)

namespace BlockDataMatch

theorem refl (a : BlockDatum.{uK,uG,uV} K G) : BlockDataMatch a a :=
  ⟨rfl, ⟨Representation.Equiv.refl _⟩⟩

theorem symm {a : BlockDatum.{uK,uG,uV} K G} {b : BlockDatum.{uK,uG,uW} K G}
    (h : BlockDataMatch a b) : BlockDataMatch b a :=
  ⟨h.1.symm, ⟨h.2.some.symm⟩⟩

theorem trans {a : BlockDatum.{uK,uG,uV} K G} {b : BlockDatum.{uK,uG,uW} K G}
    {c : BlockDatum.{uK,uG,uX} K G} (h : BlockDataMatch a b) (h' : BlockDataMatch b c) :
    BlockDataMatch a c :=
  ⟨h.1.trans h'.1, ⟨h.2.some.trans h'.2.some⟩⟩

end BlockDataMatch

/-- The matching relation on the disjoint union of two families of block data. -/
def blockIndexRel {ι : Type uι} {κ : Type uκ}
    (d : ι → BlockDatum.{uK,uG,uV} K G) (d' : κ → BlockDatum.{uK,uG,uW} K G) :
    (ι ⊕ κ) → (ι ⊕ κ) → Prop
  | .inl i, .inl j => BlockDataMatch (d i) (d j)
  | .inl i, .inr j => BlockDataMatch (d i) (d' j)
  | .inr i, .inl j => BlockDataMatch (d' i) (d j)
  | .inr i, .inr j => BlockDataMatch (d' i) (d' j)

/-- Length and Weil-factor isomorphism define a genuine equivalence relation. -/
def blockIndexSetoid {ι : Type uι} {κ : Type uκ}
    (d : ι → BlockDatum.{uK,uG,uV} K G) (d' : κ → BlockDatum.{uK,uG,uW} K G) :
    Setoid (ι ⊕ κ) where
  r := blockIndexRel d d'
  iseqv := {
    refl := by intro a; cases a <;> exact BlockDataMatch.refl _
    symm := by intro a b h; cases a <;> cases b <;> exact BlockDataMatch.symm h
    trans := by intro a b c h h'; cases a <;> cases b <;> cases c <;>
      exact BlockDataMatch.trans h h' }

/-- Counts against the data occurring in either family suffice for a matching. -/
theorem matching_of_class_counts {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ]
    (d : ι → BlockDatum.{uK,uG,uV} K G) (d' : κ → BlockDatum.{uK,uG,uW} K G)
    (hl : ∀ a, Nat.card {i // BlockDataMatch (d i) (d a)} =
      Nat.card {j // BlockDataMatch (d' j) (d a)})
    (hr : ∀ b, Nat.card {i // BlockDataMatch (d i) (d' b)} =
      Nat.card {j // BlockDataMatch (d' j) (d' b)}) :
    ∃ e : ι ≃ κ, ∀ i, (d i).length = (d' (e i)).length ∧
      Nonempty (FiniteRepresentation.Equiv (d i).representation (d' (e i)).representation) := by
  apply exists_equiv_of_setoid_card_eq (blockIndexSetoid d d')
  intro a
  cases a with
  | inl a => exact hl a
  | inr b => exact hr b

end Langlands.WeilDeligneRepresentation.Blocks
