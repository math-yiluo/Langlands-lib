/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Scheduling a small set of persistent requirements

Source: Stacks Project, Sites, Tag 00YP (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

namespace CategoryTheory

/-- If a persistent requirement can always be added, all requirements hold in some
object obtained by transfinite iteration.

Source: Stacks Project, Sites, Tag 00YP, well-ordering the set of lifting requests
(auxiliary; not a blueprint node).
Proof: Iterate a successor which adds a missing requirement. Use a well-order of
cardinality strictly larger than the set of requirements. If no stage satisfies all
requirements, choose the newly added requirement at every stage. Persistence makes
these choices injective, contrary to the cardinality of the well-order. Colimits at
limit stages exist by the hypothesis. This proof also covers an empty request set. -/
theorem exists_object_all_requirements
    {D : Type u} [Category.{v} D] [Nonempty D] {A : Type w}
    (hcolim : ∀ (B : Type w) [LinearOrder B] [Nonempty B], HasColimitsOfShape B D)
    (Satisfied : D → A → Prop)
    (persist : ∀ {X Y : D}, (X ⟶ Y) → ∀ a, Satisfied X a → Satisfied Y a)
    (extend : ∀ (X : D), (¬ ∀ a, Satisfied X a) →
      ∃ (Y : D) (_ : X ⟶ Y) (a : A), ¬ Satisfied X a ∧ Satisfied Y a) :
    ∃ X : D, ∀ a, Satisfied X a := by
  classical
  by_contra! hnone
  choose obj arrow task hmissing hadded using fun X ↦ extend X (not_forall.mpr (hnone X))
  let Φ : SmallObject.SuccStruct D :=
    ⟨Classical.arbitrary D, obj, arrow⟩
  let κ : Cardinal.{w} := Order.succ (max Cardinal.aleph0 (Cardinal.mk A))
  let B := κ.ord.ToType
  have hκ : Cardinal.aleph0 ≤ κ := (le_max_left _ _).trans (Order.le_succ _)
  have : Nonempty B := Cardinal.nonempty_ord_toType (Cardinal.aleph0_pos.trans_le hκ).ne'
  let : OrderBot B := WellFoundedLT.toOrderBot B
  let : SuccOrder B := SuccOrder.ofLinearWellFoundedLT B
  have : NoMaxOrder B := Cardinal.noMaxOrder hκ
  let : HasIterationOfShape B D := {
    hasColimitsOfShape := hcolim B
    hasColimitsOfShape_of_isSuccLimit := fun b hb ↦ by
      have : Nonempty (Set.Iio b) := hb.nonempty_Iio.to_subtype
      exact hcolim (Set.Iio b) }
  let F := Φ.iterationFunctor B
  have hf (b : B) : Satisfied (F.obj (Order.succ b)) (task (F.obj b)) := by
    have hh := Φ.prop_iterationFunctor_map_succ b (not_isMax b)
    rw [← hh.succ_eq]
    exact hadded _
  have hdiff {b c : B} (hbc : b < c) : task (F.obj b) ≠ task (F.obj c) := by
    intro heq
    apply hmissing (F.obj c)
    have hh := persist (F.map (homOfLE (Order.succ_le_of_lt hbc))) _ (hf b)
    simpa only [heq] using hh
  have hinj : Function.Injective (fun b : B ↦ task (F.obj b)) := by
    intro b c heq
    by_contra hne
    exact (lt_or_gt_of_ne hne).elim (fun h ↦ hdiff h heq) (fun h ↦ hdiff h heq.symm)
  have hle := Cardinal.mk_le_of_injective hinj
  have hlt : Cardinal.mk A < Cardinal.mk B := by
    change Cardinal.mk A < Cardinal.mk κ.ord.ToType
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact (le_max_right _ _).trans_lt (Order.lt_succ _)
  exact hlt.not_ge hle

end CategoryTheory
