/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Left/right derived functors and opposite categories

Supplement to `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

This file contains material from the PR files
`Mathlib/CategoryTheory/Functor/KanExtension/Opposite.lean` and
`Mathlib/CategoryTheory/Functor/Derived/Opposite.lean` (both new in the PR),
adapted locally: the comparison of left/right Kan extensions with their
opposites, and the resulting comparison of left/right derived functors
with their opposites.

-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C C' D D' H H' : Type*} [Category C] [Category D] [Category H] [Category H']
  [Category D'] [Category C']

namespace Functor

section

variable {L : C ⥤ D} {F : C ⥤ H}

/-- The left extension of `L.op` along `F.op` obtained from a right extension
of `L` along `F`. -/
@[simps!]
protected def RightExtension.op (E : RightExtension L F) : LeftExtension L.op F.op :=
  LeftExtension.mk (F' := E.left.op) (NatTrans.op E.hom)

/-- The right extension of `L` along `F` obtained from a right extension
of `L.op` along `F.op`. -/
@[simps!]
protected def RightExtension.unop (E : RightExtension L.op F.op) : LeftExtension L F :=
  LeftExtension.mk (F' := E.left.unop) (NatTrans.unop E.hom)

/-- The right extension of `L.op` along `F.op` obtained from a left extension
of `L` along `F`. -/
@[simps!]
protected def LeftExtension.op (E : LeftExtension L F) : RightExtension L.op F.op :=
  RightExtension.mk (F' := E.right.op) (NatTrans.op E.hom)

/-- The left extension of `L` along `F` obtained from a left extension
of `L.op` along `F.op`. -/
@[simps!]
protected def LeftExtension.unop (E : LeftExtension L.op F.op) : RightExtension L F :=
  RightExtension.mk (F' := E.right.unop) (NatTrans.unop E.hom)

variable (L F)

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `(RightExtension L F)ᵒᵖ ≌ LeftExtension L.op F.op`. -/
@[simps]
def rightExtensionOpEquivalence :
    (RightExtension L F)ᵒᵖ ≌ LeftExtension L.op F.op where
  functor :=
    { obj E := E.unop.op
      map f := StructuredArrow.homMk (NatTrans.op f.unop.left)
        (congr_arg NatTrans.op (CostructuredArrow.w f.unop)) }
  inverse :=
    { obj E := op (E.unop)
      map f := (CostructuredArrow.homMk (NatTrans.unop f.right)
        (congr_arg NatTrans.unop (StructuredArrow.w f))).op }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `(LeftExtension L F)ᵒᵖ ≌ RightExtension L.op F.op`. -/
@[simps]
def leftExtensionOpEquivalence :
    (LeftExtension L F)ᵒᵖ ≌ RightExtension L.op F.op where
  functor :=
    { obj E := E.unop.op
      map f := CostructuredArrow.homMk (NatTrans.op f.unop.right)
        (congr_arg NatTrans.op (StructuredArrow.w f.unop)) }
  inverse :=
    { obj E := op (E.unop)
      map f := (StructuredArrow.homMk (NatTrans.unop f.left)
        (congr_arg NatTrans.unop (CostructuredArrow.w f))).op }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {L F}

namespace RightExtension.IsUniversal

/-- If a right extension is universal, then so is the corresponding
left extension in the opposite categories. -/
protected noncomputable def op {E : RightExtension L F} (h : E.IsUniversal) :
    E.op.IsUniversal :=
  (initialOpOfTerminal h).isInitialObj
    ((rightExtensionOpEquivalence L F).functor)

/-- If a right extension of `L.op` along `F.op` is universal, then so is
the corresponding left extension of `L` along `F`. -/
protected noncomputable def unop {E : RightExtension L.op F.op} (h : E.IsUniversal) :
    E.unop.IsUniversal :=
  initialUnopOfTerminal
    (h.isTerminalObj (leftExtensionOpEquivalence L F).inverse)

end RightExtension.IsUniversal

namespace LeftExtension.IsUniversal

/-- If a left extension is universal, then so is the corresponding
right extension in the opposite categories. -/
noncomputable def op {E : LeftExtension L F} (h : E.IsUniversal) :
    E.op.IsUniversal :=
  (terminalOpOfInitial h).isTerminalObj
    ((leftExtensionOpEquivalence L F).functor)

/-- If a left extension of `L.op` along `F.op` is universal, then so is
the corresponding right extension of `L` along `F`. -/
noncomputable def unop {E : LeftExtension L.op F.op} (h : E.IsUniversal) :
    E.unop.IsUniversal :=
  terminalUnopOfInitial
    (h.isInitialObj (rightExtensionOpEquivalence L F).inverse)

end LeftExtension.IsUniversal

end

section

variable {F' : D ⥤ H} {L : C ⥤ D} {F : C ⥤ H}

lemma isRightKanExtension_iff_op (α : L ⋙ F' ⟶ F) :
    F'.IsRightKanExtension α ↔
      F'.op.IsLeftKanExtension (F := F.op) (L := L.op) (NatTrans.op α) :=
  ⟨fun ⟨⟨(h)⟩⟩ ↦ ⟨⟨RightExtension.IsUniversal.op h⟩⟩,
    fun ⟨⟨(h)⟩⟩ ↦ ⟨⟨LeftExtension.IsUniversal.unop h⟩⟩⟩

lemma isLeftKanExtension_iff_op (α : F ⟶ L ⋙ F') :
    F'.IsLeftKanExtension α ↔
      F'.op.IsRightKanExtension (F := F.op) (L := L.op) (NatTrans.op α) :=
  ⟨fun ⟨⟨(h)⟩⟩ ↦ ⟨⟨LeftExtension.IsUniversal.op h⟩⟩,
    fun ⟨⟨(h)⟩⟩ ↦ ⟨⟨RightExtension.IsUniversal.unop h⟩⟩⟩

instance (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α] :
    F'.op.IsLeftKanExtension (F := F.op) (L := L.op) (NatTrans.op α) := by
  rwa [← isRightKanExtension_iff_op]

instance (α : F ⟶ L ⋙ F') [F'.IsLeftKanExtension α] :
    F'.op.IsRightKanExtension (F := F.op) (L := L.op) (NatTrans.op α) := by
  rwa [← isLeftKanExtension_iff_op]

end

section

variable
  (F' : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : L ⋙ F' ⟶ F) (β : F ⟶ L ⋙ F')
  (W : MorphismProperty C) [L.IsLocalization W]

lemma isLeftDerivedFunctor_iff_op :
    F'.IsLeftDerivedFunctor α W ↔
      F'.op.IsRightDerivedFunctor (F := F.op) (L := L.op) (NatTrans.op α) W.op := by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension,
    isRightDerivedFunctor_iff_isLeftKanExtension,
    isRightKanExtension_iff_op]

lemma isRightDerivedFunctor_iff_op :
    F'.IsRightDerivedFunctor β W ↔
      F'.op.IsLeftDerivedFunctor (F := F.op) (L := L.op) (NatTrans.op β) W.op := by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension,
    isRightDerivedFunctor_iff_isLeftKanExtension,
    isLeftKanExtension_iff_op]

instance [F'.IsLeftDerivedFunctor α W] :
    F'.op.IsRightDerivedFunctor (F := F.op) (L := L.op) (NatTrans.op α) W.op := by
  rwa [← isLeftDerivedFunctor_iff_op]

instance [F'.IsRightDerivedFunctor β W] :
    F'.op.IsLeftDerivedFunctor (F := F.op) (L := L.op) (NatTrans.op β) W.op := by
  rwa [← isRightDerivedFunctor_iff_op]

end

section

variable (F : C ⥤ D) (W : MorphismProperty C)

lemma hasLeftDerivedFunctor_iff_op :
    F.HasLeftDerivedFunctor W ↔ F.op.HasRightDerivedFunctor W.op := by
  constructor
  · intro h
    exact HasRightDerivedFunctor.mk' (L := W.Q.op)
      (RF := (F.totalLeftDerived W.Q W).op)
      (α := NatTrans.op (F.totalLeftDerivedCounit W.Q W))
  · intro h
    have : (F.op.totalRightDerived W.Q.op W.op).unop.IsLeftDerivedFunctor
      (NatTrans.unop (F.op.totalRightDerivedUnit W.Q.op W.op)) W := by
      rw [isLeftDerivedFunctor_iff_op]
      exact inferInstanceAs ((F.op.totalRightDerived W.Q.op W.op).IsRightDerivedFunctor
        (F.op.totalRightDerivedUnit W.Q.op W.op) W.op)
    exact HasLeftDerivedFunctor.mk' (L := W.Q)
      (LF := (F.op.totalRightDerived W.Q.op W.op).unop)
      (α := NatTrans.unop (F.op.totalRightDerivedUnit W.Q.op W.op))

lemma hasRightDerivedFunctor_iff_op :
    F.HasRightDerivedFunctor W ↔ F.op.HasLeftDerivedFunctor W.op := by
  constructor
  · intro h
    exact HasLeftDerivedFunctor.mk' (L := W.Q.op)
      (LF := (F.totalRightDerived W.Q W).op)
      (α := NatTrans.op (F.totalRightDerivedUnit W.Q W))
  · intro h
    have : (F.op.totalLeftDerived W.Q.op W.op).unop.IsRightDerivedFunctor
      (NatTrans.unop (F.op.totalLeftDerivedCounit W.Q.op W.op)) W := by
      rw [isRightDerivedFunctor_iff_op]
      exact inferInstanceAs ((F.op.totalLeftDerived W.Q.op W.op).IsLeftDerivedFunctor
        (F.op.totalLeftDerivedCounit W.Q.op W.op) W.op)
    exact HasRightDerivedFunctor.mk' (L := W.Q)
      (RF := (F.op.totalLeftDerived W.Q.op W.op).unop)
      (α := NatTrans.unop (F.op.totalLeftDerivedCounit W.Q.op W.op))


end

section

variable (LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D}
  (α : L ⋙ LF ⟶ F) (W : MorphismProperty C) [L.IsLocalization W]

set_option backward.defeqAttrib.useBackward true in
instance [IsIso α] : LF.IsLeftDerivedFunctor α W where
  isRightKanExtension :=
    letI lifting : Localization.Lifting L W F LF := ⟨asIso α⟩
    ⟨⟨IsTerminal.ofUniqueHom
      (fun G => CostructuredArrow.homMk
        (Localization.liftNatTrans L W (L ⋙ G.left) F G.left LF G.hom) (by
          ext X
          dsimp
          simp only [Localization.liftNatTrans_app, comp_obj, Category.assoc]
          dsimp [Localization.Lifting.iso, lifting]
          simp only [NatIso.isIso_inv_app, comp_obj, IsIso.inv_hom_id,
            Category.comp_id, Category.id_comp]))
      (fun G φ => by
        ext1
        apply Localization.natTrans_ext L W
        intro X
        dsimp
        simp only [Localization.liftNatTrans_app, comp_obj]
        dsimp [Localization.Lifting.iso, lifting]
        simpa using NatTrans.congr_app φ.w X)⟩⟩

example (G : D ⥤ H) : G.IsLeftDerivedFunctor (𝟙 (L ⋙ G)) W := inferInstance

instance (G : D ⥤ H) : (L ⋙ G).HasLeftDerivedFunctor W :=
  HasLeftDerivedFunctor.mk' G (𝟙 _)

end

end Functor

end CategoryTheory
