/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties

/-! # Small triangulated hulls closed under bounded coproducts

Source: Krause (2001), Lemma 5(1), page 124.
(blueprint: lem-sfb-small-bounded-triangulated-hull)
-/

@[expose] public section

universe v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasCoproducts.{v} C]

private def boundedSums (α : Cardinal.{v}) (P : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∃ (I : Type v) (Y : I → C), HasCardinalLT I α ∧
    (∀ i, P (Y i)) ∧ Nonempty (X ≅ ∐ Y)

private def hullStep (α : Cardinal.{v}) (P : ObjectProperty C) : ObjectProperty C :=
  (P.shiftClosure ℤ ⊔ ObjectProperty.extensionProduct P P ⊔ boundedSums α P).isoClosure

private theorem le_hullStep (α : Cardinal.{v}) (P : ObjectProperty C) :
    P ≤ hullStep α P :=
  P.le_shiftClosure.trans ((le_sup_left.trans le_sup_left).trans
    (ObjectProperty.le_isoClosure _))

private theorem hullStep_small (α : Cardinal.{v}) (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{v} P] :
    ObjectProperty.EssentiallySmall.{v} (hullStep α P) := by
  have : ObjectProperty.EssentiallySmall.{v} (P.shiftClosure ℤ) :=
    ObjectProperty.EssentiallySmall.shiftClosure P
  have : ObjectProperty.EssentiallySmall.{v} (ObjectProperty.extensionProduct P P) :=
    ObjectProperty.EssentiallySmall.extensionProduct P P
  have : ObjectProperty.EssentiallySmall.{v} (boundedSums α P) :=
    ObjectProperty.EssentiallySmall.bounded_coproducts P α
  exact inferInstanceAs (ObjectProperty.EssentiallySmall.{v}
    (P.shiftClosure ℤ ⊔ ObjectProperty.extensionProduct P P ⊔ boundedSums α P).isoClosure)

private theorem hullStep_le (α : Cardinal.{v}) (P S : ObjectProperty C)
    [S.IsTriangulated] [S.IsClosedUnderIsomorphisms] (hPS : P ≤ S)
    (hsum : ∀ (I : Type v) (Y : I → C), HasCardinalLT I α →
      (∀ i, S (Y i)) → S (∐ Y)) : hullStep α P ≤ S := by
  change (P.shiftClosure ℤ ⊔ ObjectProperty.extensionProduct P P ⊔
    boundedSums α P).isoClosure ≤ S
  rw [ObjectProperty.isoClosure_le_iff]
  rintro X ((hshift | hext) | hcop)
  · obtain ⟨Y, n, e, hY⟩ := hshift
    exact S.prop_of_iso e.symm (S.le_shift n _ (hPS _ hY))
  · obtain ⟨Y, Z, a, b, c, hT, hY, hZ⟩ := hext
    exact S.ext_of_isTriangulatedClosed₂ _ hT (hPS _ hY) (hPS _ hZ)
  · obtain ⟨I, Y, hI, hY, ⟨e⟩⟩ := hcop
    exact S.prop_of_iso e.symm (hsum I Y hI (fun i ↦ hPS _ (hY i)))

private def zeroClass : ObjectProperty C := ObjectProperty.pair (0 : C) 0

private noncomputable def hullStage (G : ObjectProperty C) (α : Cardinal.{v})
    (i : α.ord.ToType) : ObjectProperty C :=
  WellFounded.fix (wellFounded_lt : WellFounded ((· < ·) : α.ord.ToType → _ → Prop))
    (fun i rec ↦ hullStep α (G ⊔ zeroClass ⊔ ⨆ j : Set.Iio i, rec j.val j.property)) i

private theorem hullStage_eq (G : ObjectProperty C) (α : Cardinal.{v})
    (i : α.ord.ToType) : hullStage G α i =
      hullStep α (G ⊔ zeroClass ⊔ ⨆ j : Set.Iio i, hullStage G α j.val) := by
  unfold hullStage
  rw [WellFounded.fix_eq]

private theorem stage_small (G : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{v} G] (α : Cardinal.{v}) (i : α.ord.ToType) :
    ObjectProperty.EssentiallySmall.{v} (hullStage G α i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [hullStage_eq]
    have : ∀ j : Set.Iio i, ObjectProperty.EssentiallySmall.{v}
        (hullStage G α j.val) := fun j ↦ ih j.val j.property
    have : ObjectProperty.EssentiallySmall.{v} (zeroClass (C := C)) :=
      inferInstanceAs (ObjectProperty.EssentiallySmall.{v} (ObjectProperty.pair (0 : C) 0))
    exact hullStep_small α _

private theorem stage_le (G S : ObjectProperty C)
    [S.IsTriangulated] [S.IsClosedUnderIsomorphisms] (α : Cardinal.{v}) (hGS : G ≤ S)
    (hsum : ∀ (I : Type v) (Y : I → C), HasCardinalLT I α →
      (∀ i, S (Y i)) → S (∐ Y)) (i : α.ord.ToType) : hullStage G α i ≤ S := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [hullStage_eq]
    apply hullStep_le α _ S _ hsum
    refine sup_le (sup_le hGS ?_) (iSup_le fun j ↦ ih j.val j.property)
    intro X hX
    have hz : 0 = X := by simpa only [zeroClass, ObjectProperty.pair_iff, or_self] using hX
    subst X
    exact S.prop_zero

private theorem stages_bounded (α : Cardinal.{v}) [Fact α.IsRegular]
    {I : Type v} (hI : HasCardinalLT I α) (f : I → α.ord.ToType) :
    ∃ j, ∀ i, f i < j := by
  let g : I → Ordinal.{v} := fun i ↦ (f i).toOrd.val
  have hg : ∀ i, g i < α.ord := fun i ↦ (f i).toOrd.property
  have hcard : Cardinal.mk I < α.ord.cof := by
    rw [(Fact.out : α.IsRegular).cof_ord]
    exact (hasCardinalLT_iff_cardinal_mk_lt I α).mp hI
  have hb := Ordinal.iSup_add_one_lt_of_lt_cof hcard hg
  let j : α.ord.ToType := Ordinal.ToType.mk ⟨⨆ i, g i + 1, hb⟩
  refine ⟨j, fun i ↦ ?_⟩
  apply (Ordinal.ToType.mk.symm.lt_iff_lt).mp
  change g i < (Ordinal.ToType.mk.symm (Ordinal.ToType.mk _)).val
  rw [OrderIso.symm_apply_apply]
  exact (Order.lt_succ (g i)).trans_le (Ordinal.le_iSup _ i)

/-- Inside a triangulated class closed under coproducts of fewer than alpha
summands, every essentially small family lies in a class with the same closure
properties which is still essentially small.
Source: Krause (2001), Lemma 5(1), page 124, explicit small hull construction.
(blueprint: lem-sfb-small-bounded-triangulated-hull)

Proof: at each stage adjoin shifts, middle vertices of triangles and coproducts
of fewer than alpha inputs, then take isomorphism closure. Start with G and
zero, and include all earlier stages at each step. Each stage is essentially
small by the smallness APIs for shifts, extensions and bounded coproducts.
Index the stages by the initial ordinal of alpha. The union is essentially
small since this index type is small. Regularity puts every family of fewer
than alpha input stages strictly below one stage, so the union has all the
required closure properties. Every stage stays inside S by induction. -/
theorem exists_small_bounded_triangulated_hull
    (G S : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} G]
    [S.IsClosedUnderIsomorphisms] [S.IsTriangulated]
    (α : Cardinal.{v}) [Fact α.IsRegular] (hGS : G ≤ S)
    (hsum : ∀ (I : Type v) (Y : I → C), HasCardinalLT I α →
      (∀ i, S (Y i)) → S (∐ Y)) :
    ∃ H : ObjectProperty C, ObjectProperty.EssentiallySmall.{v} H ∧
      H.IsClosedUnderIsomorphisms ∧ H.IsTriangulated ∧ G ≤ H ∧ H ≤ S ∧
      (∀ (I : Type v) (Y : I → C), HasCardinalLT I α →
        (∀ i, H (Y i)) → H (∐ Y)) := by
  classical
  let H : ObjectProperty C := ⨆ i : α.ord.ToType, hullStage G α i
  have : ∀ i, ObjectProperty.EssentiallySmall.{v} (hullStage G α i) :=
    stage_small G α
  have hsmall : ObjectProperty.EssentiallySmall.{v} H := inferInstanceAs
    (ObjectProperty.EssentiallySmall.{v} (⨆ i : α.ord.ToType, hullStage G α i))
  have : ∀ i, (hullStage G α i).IsClosedUnderIsomorphisms := by
    intro i
    rw [hullStage_eq]
    dsimp only [hullStep]
    infer_instance
  have hiso : H.IsClosedUnderIsomorphisms := inferInstanceAs
    (⨆ i : α.ord.ToType, hullStage G α i).IsClosedUnderIsomorphisms
  let B (i : α.ord.ToType) : ObjectProperty C :=
    G ⊔ zeroClass ⊔ ⨆ j : Set.Iio i, hullStage G α j.val
  have hstep (i : α.ord.ToType) : hullStep α (B i) ≤ H := by
    rw [show hullStep α (B i) = hullStage G α i from (hullStage_eq G α i).symm]
    exact le_iSup (fun i ↦ hullStage G α i) i
  have hprev {i j : α.ord.ToType} (hij : i < j) : hullStage G α i ≤ B j :=
    le_sup_right.trans' (le_iSup (fun k : Set.Iio j ↦ hullStage G α k.val) ⟨i, hij⟩)
  have hlim := Cardinal.isSuccLimit_ord (Fact.out : α.IsRegular).aleph0_le
  have : NoMaxOrder α.ord.ToType := Ordinal.isSuccPrelimit_type_lt_iff.mp
    (by simpa only [Ordinal.type_toType] using hlim.isSuccPrelimit)
  have : Nonempty α.ord.ToType := Ordinal.nonempty_toType_iff.mpr
    (Fact.out : α.IsRegular).ord_pos.ne'
  let i₀ : α.ord.ToType := Classical.arbitrary _
  have hGH : G ≤ H :=
    (le_sup_left.trans le_sup_left).trans ((le_hullStep α (B i₀)).trans (hstep i₀))
  have hzero : H (0 : C) := by
    apply (le_hullStep α (B i₀)).trans (hstep i₀)
    exact Or.inl (Or.inr (by simp [zeroClass]))
  have : H.ContainsZero := ⟨0, isZero_zero C, hzero⟩
  have : H.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX
    obtain ⟨i, hi⟩ := (ObjectProperty.prop_iSup_iff _ _).mp hX
    obtain ⟨j, hij⟩ := exists_gt i
    apply hstep j
    apply ObjectProperty.le_isoClosure
    exact Or.inl (Or.inl ⟨X, n, Iso.refl _, hprev hij X hi⟩)⟩⟩
  have : H.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃
    obtain ⟨i, hi⟩ := (ObjectProperty.prop_iSup_iff _ _).mp h₁
    obtain ⟨j, hj⟩ := (ObjectProperty.prop_iSup_iff _ _).mp h₃
    obtain ⟨k, hk⟩ := exists_gt (max i j)
    apply hstep k
    apply ObjectProperty.le_isoClosure
    exact Or.inl (Or.inr ⟨_, _, _, _, _, hT,
      hprev ((le_max_left i j).trans_lt hk) _ hi,
      hprev ((le_max_right i j).trans_lt hk) _ hj⟩))
  have htri : H.IsTriangulated := {}
  refine ⟨H, hsmall, hiso, htri, hGH, iSup_le (stage_le G S α hGS hsum), ?_⟩
  intro I Y hI hY
  choose f hf using fun i ↦ (ObjectProperty.prop_iSup_iff _ _).mp (hY i)
  obtain ⟨j, hj⟩ := stages_bounded α hI f
  apply hstep j
  apply ObjectProperty.le_isoClosure
  exact Or.inr ⟨I, Y, hI, fun i ↦ hprev (hj i) _ (hf i), ⟨Iso.refl _⟩⟩

end CategoryTheory
