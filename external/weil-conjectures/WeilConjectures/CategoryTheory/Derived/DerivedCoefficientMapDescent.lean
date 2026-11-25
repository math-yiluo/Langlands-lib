/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

/-! # Descent of a termwise coefficient map
Source: Stacks Project, Tags 06XN, 05SU and 06YY.
(blueprint: lem-sbc-derived-coefficient-map-descent)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

private theorem kanPostShift
    {D D' L : Type*} [Category D] [HasShift D ℤ]
    [Category D'] [HasShift D' ℤ] [Category L] [HasShift L ℤ]
    (F : D ⥤ D') (Q : D ⥤ L)
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ) :
    (LF ⋙ shiftFunctor D' n).IsRightKanExtension
      ((associator Q LF (shiftFunctor D' n)).inv ≫
        whiskerRight α (shiftFunctor D' n)) := by
  let P := RightExtension.postcompose₂ Q F (shiftFunctor D' n)
  let : IsIso (𝟙 (F ⋙ shiftFunctor D' n)) := by infer_instance
  let : P.IsEquivalence := by
    dsimp [P, RightExtension.postcompose₂]
    let t : ((whiskeringRight L D' D').obj (shiftFunctor D' n)) ⋙
        (whiskeringLeft D L D').obj Q ⟶
        (whiskeringLeft D L D').obj Q ⋙
          ((whiskeringRight D D' D').obj (shiftFunctor D' n)) :=
      { app G := (associator Q G (shiftFunctor D' n)).inv }
    let : IsIso t := by apply NatIso.isIso_of_isIso_app
    exact CostructuredArrow.isEquivalenceMap₂ t (𝟙 _)
  constructor
  refine ⟨Limits.IsTerminal.ofIso
    (Limits.IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact RightExtension.postcompose₂ObjMkIso (shiftFunctor D' n) α

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_of_precomp_quotient
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] {H : Type w} [Category.{w'} H]
    (L : HomotopyCategory A (.up ℤ) ⥤ D)
    (G : HomotopyCategory A (.up ℤ) ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G)
    (h : F.IsRightKanExtension
      ((associator (HomotopyCategory.quotient A (.up ℤ)) L F).hom ≫
        whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) α)) :
    F.IsRightKanExtension α := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have : ((whiskeringLeft _ _ H).obj q).Full := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Full)
  have : ((whiskeringLeft _ _ H).obj q).Faithful := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Faithful)
  let P := RightExtension.precomp L G q
  have : P.Full := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.full_map₂
  have : P.Faithful := by
    dsimp [P, RightExtension.precomp]
    infer_instance
  let β := (associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  let := h
  exact ⟨⟨IsTerminal.isTerminalOfObj P _
    (IsTerminal.ofIso (F.isUniversalOfIsRightKanExtension β) e.symm)⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {G G' : C ⥤ H} (F : D ⥤ H)
    (i : Q ≅ Q') (j : G ≅ G') (α : Q ⋙ F ⟶ G)
    [F.IsRightKanExtension α] :
    F.IsRightKanExtension (whiskerRight i.inv F ≫ α ≫ j.hom) := by
  let P := (rightExtensionEquivalenceOfIso₁ i G).functor ⋙
    (rightExtensionEquivalenceOfIso₂ Q' j).functor
  constructor
  refine ⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact CostructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [P, rightExtensionEquivalenceOfIso₁, rightExtensionEquivalenceOfIso₂])

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_precomp_quotient
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] {H : Type w} [Category.{w'} H]
    (L : HomotopyCategory A (.up ℤ) ⥤ D)
    (G : HomotopyCategory A (.up ℤ) ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G) [F.IsRightKanExtension α] :
    F.IsRightKanExtension
      ((associator (HomotopyCategory.quotient A (.up ℤ)) L F).hom ≫
        whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) α) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have : ((whiskeringLeft _ _ H).obj q).Full := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Full)
  have : ((whiskeringLeft _ _ H).obj q).Faithful := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Faithful)
  let P := RightExtension.precomp L G q
  have : P.IsEquivalence := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.isEquivalenceMap₂
  let β := (associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  exact ⟨⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) e⟩⟩

end CategoryTheory.Functor
