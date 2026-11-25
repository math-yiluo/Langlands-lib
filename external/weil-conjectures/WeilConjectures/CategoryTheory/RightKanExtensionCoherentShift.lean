/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-! # Shift structures on right Kan extensions

Source: Stacks Project, Derived Categories, Tag 05SU and Proposition Tag 05SE.
(blueprint: lem-pur-right-kan-extension-coherent-shift).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

@[expose] public section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

private theorem kanPostShift
    {D : Type u} [Category.{v} D] [HasShift D ℤ]
    {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
    {L : Type u''} [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ]
    (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ) :
    (LF ⋙ shiftFunctor D' n).IsRightKanExtension
      ((associator Q LF (shiftFunctor D' n)).inv ≫ whiskerRight α (shiftFunctor D' n)) := by
  let P := RightExtension.postcompose₂ Q F (shiftFunctor D' n)
  let : IsIso (𝟙 (F ⋙ shiftFunctor D' n)) := by infer_instance
  let : P.IsEquivalence := by
    dsimp [P, RightExtension.postcompose₂]
    let t : ((whiskeringRight L D' D').obj (shiftFunctor D' n)) ⋙
        (whiskeringLeft D L D').obj Q ⟶
        (whiskeringLeft D L D').obj Q ⋙
          ((whiskeringRight D D' D').obj (shiftFunctor D' n)) :=
      { app G := (associator Q G (shiftFunctor D' n)).inv }
    let : IsIso t := by
      apply NatIso.isIso_of_isIso_app
    exact CostructuredArrow.isEquivalenceMap₂ t (𝟙 _)
  constructor
  refine ⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact RightExtension.postcompose₂ObjMkIso (shiftFunctor D' n) α

private noncomputable def kanShiftIso
    {D : Type u} [Category.{v} D] [HasShift D ℤ]
    {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
    {L : Type u''} [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ]
    (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ) :
    shiftFunctor L n ⋙ LF ≅ LF ⋙ shiftFunctor D' n := by
  let β := (associator (shiftFunctor D n) Q LF).hom ≫
    whiskerLeft (shiftFunctor D n) α
  have : LF.IsRightKanExtension β :=
    (isRightKanExtension_iff_precomp LF (shiftFunctor D n) α).1 inferInstance
  let δ := (associator Q (shiftFunctor L n) LF).inv ≫
    whiskerRight (Q.commShiftIso n).inv LF ≫ β
  have : (shiftFunctor L n ⋙ LF).IsRightKanExtension δ :=
    (isRightKanExtension_iff_postcomp₁ (shiftFunctor L n) (Q.commShiftIso n).symm β).1
      inferInstance
  let γ := (associator Q LF (shiftFunctor D' n)).inv ≫
    whiskerRight α (shiftFunctor D' n)
  have : (LF ⋙ shiftFunctor D' n).IsRightKanExtension γ := kanPostShift F Q LF α n
  exact rightKanExtensionUniqueOfIso _ δ (F.commShiftIso n) _ γ


private lemma kanShiftIso_compat
    {D : Type u} [Category.{v} D] [HasShift D ℤ]
    {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
    {L : Type u''} [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ]
    (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ) (X : D) :
    LF.map ((Q.commShiftIso n).hom.app X) ≫
      (kanShiftIso F Q LF α n).hom.app (Q.obj X) ≫
        (shiftFunctor D' n).map (α.app X) =
      α.app ((shiftFunctor D n).obj X) ≫ (F.commShiftIso n).hom.app X := by
  let γ := (associator Q LF (shiftFunctor D' n)).inv ≫
    whiskerRight α (shiftFunctor D' n)
  let δ := (associator Q (shiftFunctor L n) LF).inv ≫
    whiskerRight (Q.commShiftIso n).inv LF ≫
      (associator (shiftFunctor D n) Q LF).hom ≫ whiskerLeft (shiftFunctor D n) α
  let : (LF ⋙ shiftFunctor D' n).IsRightKanExtension γ := kanPostShift F Q LF α n
  have h := (LF ⋙ shiftFunctor D' n).liftOfIsRightKanExtension_fac_app γ
    (shiftFunctor L n ⋙ LF) (δ ≫ (F.commShiftIso n).hom) X
  simp only [γ, δ, NatTrans.comp_app, associator_inv_app, associator_hom_app,
    whiskerRight_app, whiskerLeft_app, Category.id_comp] at h
  dsimp only [kanShiftIso, rightKanExtensionUniqueOfIso]
  simp only [Category.assoc] at h ⊢
  rw [h]
  simp only [← LF.map_comp_assoc, Iso.hom_inv_id_app, LF.map_id, Category.id_comp]

private lemma kanShiftHom_ext
    {D : Type u} [Category.{v} D] [HasShift D ℤ]
    {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
    {L : Type u''} [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ]
    (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ)
    {G : L ⥤ D'} (f g : G ⟶ LF ⋙ shiftFunctor D' n)
    (h : ∀ X : D, f.app (Q.obj X) ≫ (shiftFunctor D' n).map (α.app X) =
      g.app (Q.obj X) ≫ (shiftFunctor D' n).map (α.app X)) : f = g := by
  let γ := (associator Q LF (shiftFunctor D' n)).inv ≫
    whiskerRight α (shiftFunctor D' n)
  let : (LF ⋙ shiftFunctor D' n).IsRightKanExtension γ := kanPostShift F Q LF α n
  apply (LF ⋙ shiftFunctor D' n).hom_ext_of_isRightKanExtension γ
  ext X
  simpa [γ] using h X

private lemma kanShiftIso_zero
    {D : Type u} [Category.{v} D] [HasShift D ℤ]
    {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
    {L : Type u''} [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ]
    (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] :
    kanShiftIso F Q LF α 0 = CommShift.isoZero LF ℤ := by
  apply Iso.ext
  apply kanShiftHom_ext F Q LF α 0
  intro X
  apply (cancel_epi (LF.map ((Q.commShiftIso 0).hom.app X))).mp
  rw [kanShiftIso_compat]
  simp only [commShiftIso_zero, CommShift.isoZero_hom_app, Category.assoc,
    ← LF.map_comp_assoc, Iso.inv_hom_id_app]
  rw [← α.naturality_assoc]
  have h := (shiftFunctorZero D' ℤ).inv.naturality (α.app X)
  dsimp at h
  simpa only [Functor.comp_map, Functor.id_obj, Category.comp_id] using
    congrArg (fun f ↦ LF.map (Q.map ((shiftFunctorZero D ℤ).hom.app X)) ≫ f) h

private lemma kanShiftIso_add
    {D : Type u} [Category.{v} D] [HasShift D ℤ]
    {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
    {L : Type u''} [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ]
    (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (a b : ℤ) :
    kanShiftIso F Q LF α (a + b) =
      CommShift.isoAdd (kanShiftIso F Q LF α a) (kanShiftIso F Q LF α b) := by
  apply Iso.ext
  apply kanShiftHom_ext F Q LF α (a + b)
  intro X
  apply (cancel_epi (LF.map ((Q.commShiftIso (a + b)).hom.app X))).mp
  rw [kanShiftIso_compat]
  simp only [commShiftIso_add, CommShift.isoAdd_hom_app, LF.map_comp,
    Category.assoc]
  simp only [← LF.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [LF.map_comp, Category.assoc]
  erw [LF.map_id, Category.id_comp]
  have hnat := (kanShiftIso F Q LF α b).hom.naturality
    ((Q.commShiftIso a).hom.app X)
  dsimp at hnat
  rw [reassoc_of% hnat]
  have hz := (shiftFunctorAdd D' a b).inv.naturality (α.app X)
  dsimp at hz
  rw [← hz]
  rw [← (shiftFunctor D' b).map_comp_assoc, ← (shiftFunctor D' b).map_comp_assoc]
  simp only [Category.assoc]
  rw [kanShiftIso_compat, (shiftFunctor D' b).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% kanShiftIso_compat F Q LF α b ((shiftFunctor D a).obj X)]
  rw [← α.naturality_assoc]
  rfl


/-- A right Kan extension inherits coherent integer shifts from its two input functors.
Source: Stacks Project, Derived Categories, Tag 05SU and Proposition Tag 05SE;
the universal-property argument assembling the shift comparisons.
(blueprint: lem-pur-right-kan-extension-coherent-shift).

Proof: For each integer n, precomposition with the shift equivalence on the source and
postcomposition with the shift equivalence on the target preserve right Kan extensions.
The shift isomorphisms of Q and F therefore exhibit both shifted copies of LF as right
Kan extensions of the same functor. Their unique comparison gives an isomorphism
shiftFunctor L n ⋙ LF ≅ LF ⋙ shiftFunctor D' n. The comparison is characterized by the
commuting square with alpha. For n = 0, the standard unit comparison satisfies that
square, so Kan uniqueness identifies it with the constructed comparison. For a + b,
the composite of the a and b comparisons satisfies the same square as the a + b
comparison, using the coherence laws of Q and F; Kan uniqueness identifies them.
These equations give CommShift, and the defining square gives NatTrans.CommShift alpha.
No choice of a value of a mere existence statement is used: each comparison is determined
uniquely by the right Kan universal property. -/
theorem rightKanExtension_coherentShift
    {D : Type u} [Category.{v} D] [HasShift D ℤ]
    {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
    {L : Type u''} [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ]
    (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) (hLF : LF.IsRightKanExtension α) :
    ∃ (hshift : LF.CommShift ℤ),
      letI := hshift
      NatTrans.CommShift α ℤ := by
  classical
  let : LF.IsRightKanExtension α := hLF
  let hshift : LF.CommShift ℤ :=
    { commShiftIso := kanShiftIso F Q LF α
      commShiftIso_zero := kanShiftIso_zero F Q LF α
      commShiftIso_add := kanShiftIso_add F Q LF α }
  let : LF.CommShift ℤ := hshift
  refine ⟨hshift, ⟨fun n ↦ ?_⟩⟩
  ext X
  dsimp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, CommShift.comp,
    commShiftIso, hshift]
  simpa using kanShiftIso_compat F Q LF α n X


end CategoryTheory.Functor
