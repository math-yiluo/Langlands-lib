/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
/-! # Canonical section systems with Grothendieck coefficients -/
@[expose] public section
universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Sections of an inverse image, evaluated on base changes of étale objects. -/
noncomputable def Etale.grothendieckRelativeSections {R S : Scheme.{u}} (f : S ⟶ R)
    (F : Sheaf R.smallEtaleTopology A) : R.Etaleᵒᵖ ⥤ A :=
  f.Etale.op ⋙ ((Etale.upperStar A f).obj F).obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unit, inverse-image composition, and fibre-product pasting comparison.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2.
Whisker the adjunction unit by the opposite base-change functor of f, then whisker the
inverse-image composition isomorphism, and finally whisker the opposite pullback-pasting natural
transformation by the target presheaf. All three transformations are natural, so their composition
is natural. For the composite-unit formula, evaluate the unit compatibility of the inverse-image
composition isomorphism, use naturality of its inverse, and cancel the isomorphic pasting
restriction. No elements of A are used.
(auxiliary; not a blueprint node) -/
noncomputable def Etale.grothendieckRelativeSectionMap {R S T : Scheme.{u}}
    (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (F : Sheaf R.smallEtaleTopology A) :
    Etale.grothendieckRelativeSections A f F ⟶ Etale.grothendieckRelativeSections A k F :=
  Functor.whiskerLeft f.Etale.op
      ((Etale.upperStarLowerStarAdjunction A h).unit.app
        ((Etale.upperStar A f).obj F)).hom ≫
    Functor.whiskerLeft (f.Etale ⋙ h.Etale).op
      ((Etale.upperStarComp A h f k hk.symm).inv.app F).hom ≫
    Functor.whiskerRight
      (NatTrans.op
        (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f k hk.symm).hom)
      ((Etale.upperStar A k).obj F).obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The composite unit on sections, before the final pullback pasting restriction. -/
theorem Etale.section_unit_comp {R S T : Scheme.{u}} (h : S ⟶ R) (g : T ⟶ S)
    (G : Sheaf R.smallEtaleTopology A) (U : R.Etale) :
    ((Etale.upperStarLowerStarAdjunction A h).unit.app G).hom.app (op U) ≫
      ((Etale.upperStarLowerStarAdjunction A g).unit.app
        ((Etale.upperStar A h).obj G)).hom.app (op (h.Etale.obj U)) ≫
      ((Etale.upperStarComp A g h).inv.app G).hom.app
        (op (g.Etale.obj (h.Etale.obj U))) =
    ((Etale.upperStarLowerStarAdjunction A (g ≫ h)).unit.app G).hom.app (op U) ≫
      ((Etale.upperStar A (g ≫ h)).obj G).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).inv.app U).op := by
  let p := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h
  have hh := NatTrans.congr_app (congrArg (fun e ↦ e.hom)
    (Etale.upperStarComp_hom_app_unit_app A g h G)) (op U)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Etale.lowerStarComp_hom_app_hom_app, Adjunction.comp_unit_app] at hh
  change ((Etale.upperStarLowerStarAdjunction A (g ≫ h)).unit.app G).hom.app (op U) ≫
      ((Etale.upperStarComp A g h).hom.app G).hom.app (op ((g ≫ h).Etale.obj U)) =
    (((Etale.upperStarLowerStarAdjunction A h).unit.app G).hom.app (op U) ≫
      ((Etale.upperStarLowerStarAdjunction A g).unit.app
        ((Etale.upperStar A h).obj G)).hom.app (op (h.Etale.obj U))) ≫
      ((Etale.upperStar A g).obj ((Etale.upperStar A h).obj G)).obj.map
        (p.hom.app U).op at hh
  apply (cancel_mono (((Etale.upperStar A (g ≫ h)).obj G).obj.map
    (p.hom.app U).op)).1
  simp only [Category.assoc]
  erw [← (((Etale.upperStarComp A g h).inv.app G).hom.naturality
    (p.hom.app U).op)]
  dsimp only [p] at *
  simp only [← Functor.map_comp, ← op_comp, Iso.hom_inv_id_app,
    op_id]
  simp only [Category.assoc, Functor.comp_obj] at *
  erw [← reassoc_of% hh]
  have hi := NatTrans.congr_app (congrArg (fun t ↦ t.hom)
    ((Etale.upperStarComp A g h).hom_inv_id_app G)) (op ((g ≫ h).Etale.obj U))
  have he := congrArg
      (((Etale.upperStarLowerStarAdjunction A (g ≫ h)).unit.app G).hom.app (op U) ≫ ·) hi
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at he
  dsimp only [Scheme.Hom.Etale] at he
  erw [CategoryTheory.Functor.map_id]
  exact he

end AlgebraicGeometry
