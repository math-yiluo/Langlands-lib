/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Left derived functors and equivalences of categories

Right Kan extensions, and hence left derived functors, are transported along equivalences of
categories, both on the target and on the localized source.

## Main statements

* `CategoryTheory.Functor.isRightKanExtension_comp_of_isEquivalence`: if `F'` is a right Kan
  extension of `F` along `L` with counit `α`, and `G` is an equivalence, then `F' ⋙ G` is a right
  Kan extension of `F ⋙ G` along `L`.
* `CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_isEquivalence`: if `LF` is a left derived
  functor of `F`, then `LF ⋙ G` is a left derived functor of `F ⋙ G` for an equivalence `G`.
* `CategoryTheory.Functor.isLeftDerivedFunctor_precomp_of_isEquivalence`: if `L` and `L'` are two
  localization functors for the same class of morphisms and `G` is an equivalence with
  `L ⋙ G ≅ L'`, then a left derived functor `LF` of `F` along `L'` gives the left derived functor
  `G ⋙ LF` of `F` along `L`.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D D' H H' : Type*} [Category* C] [Category* D] [Category* D'] [Category* H]
  [Category* H']

/-- Postcomposition with an equivalence preserves right Kan extensions. -/
lemma isRightKanExtension_comp_of_isEquivalence {L : C ⥤ D} {F : C ⥤ H} (F' : D ⥤ H)
    (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α] (G : H ⥤ H') [G.IsEquivalence] :
    (F' ⋙ G).IsRightKanExtension ((associator _ _ _).inv ≫ whiskerRight α G) := by
  have : (RightExtension.postcompose₂ L F G).IsEquivalence :=
    inferInstanceAs (CostructuredArrow.map₂ (S := (whiskeringLeft C D H).obj L) (T := F)
      (U := (whiskeringLeft C D H').obj L) (V := F ⋙ G) (F := (whiskeringRight D H H').obj G)
      (G := (whiskeringRight C H H').obj G)
      (NatIso.ofComponents (fun _ ↦ (associator _ _ _).symm) (by cat_disch)).hom
      (𝟙 _)).IsEquivalence
  exact ⟨⟨Limits.IsTerminal.ofIso (Limits.IsTerminal.isTerminalObj
    (RightExtension.postcompose₂ L F G) _ (F'.isUniversalOfIsRightKanExtension α))
    (RightExtension.postcompose₂ObjMkIso G α)⟩⟩

/-- Postcomposition with an equivalence preserves left derived functors. -/
lemma isLeftDerivedFunctor_comp_of_isEquivalence {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H)
    (α : L ⋙ LF ⟶ F) (W : MorphismProperty C) [L.IsLocalization W]
    [LF.IsLeftDerivedFunctor α W] (G : H ⥤ H') [G.IsEquivalence] :
    (LF ⋙ G).IsLeftDerivedFunctor ((associator _ _ _).inv ≫ whiskerRight α G) W := by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact isRightKanExtension_comp_of_isEquivalence LF α G

/-- Change of localization: if `L ⋙ G ≅ L'` for an equivalence `G`, a left derived functor `LF`
of `F` along `L'` gives the left derived functor `G ⋙ LF` of `F` along `L`. -/
lemma isLeftDerivedFunctor_precomp_of_isEquivalence {L : C ⥤ D} {L' : C ⥤ D'}
    (G : D ⥤ D') [G.IsEquivalence] (e : L ⋙ G ≅ L') {F : C ⥤ H} (LF : D' ⥤ H)
    (α : L' ⋙ LF ⟶ F) (W : MorphismProperty C) [L.IsLocalization W] [L'.IsLocalization W]
    [LF.IsLeftDerivedFunctor α W] :
    (G ⋙ LF).IsLeftDerivedFunctor ((associator _ _ _).inv ≫ whiskerRight e.hom LF ≫ α) W := by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact (isRightKanExtension_iff_postcomp₁ G e α).1 inferInstance

end CategoryTheory.Functor
