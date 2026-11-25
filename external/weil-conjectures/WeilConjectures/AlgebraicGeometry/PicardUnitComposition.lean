/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-! # Composition coherence for Picard pullback comparisons

Source: Stacks Project, Tags 0095 and 0096.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackUnitIso_comp_inv
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) :
    (pullbackObjUnitIso (k ≫ l)).inv ≫
        (pullbackComp k l).inv.app (SheafOfModules.unit X.ringCatSheaf) =
      (pullbackObjUnitIso k).inv ≫ (pullback k).map (pullbackObjUnitIso l).inv := by
  apply unit_hom_ext
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  erw [← pullbackSection_one_eq (k ≫ l)]
  erw [← pullbackSection_pullbackSection k l (M := unit X) (U := ⊤)]
  erw [← pullbackSection_one_eq k]
  erw [pullbackSection_one_eq l]
  exact (pullbackUnit_naturality_apply k (pullbackObjUnitIso l).inv ⊤
    (1 : Γ(Y, ⊤))).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackUnitIso_comp
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) :
    (pullback k).map (pullbackObjUnitIso l).hom ≫ (pullbackObjUnitIso k).hom =
      (pullbackComp k l).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (pullbackObjUnitIso (k ≫ l)).hom := by
  have h : (pullback k).mapIso (pullbackObjUnitIso l) ≪≫ pullbackObjUnitIso k =
      (pullbackComp k l).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
        pullbackObjUnitIso (k ≫ l) := by
    apply Iso.ext_inv
    exact (pullbackUnitIso_comp_inv k l).symm
  exact congrArg Iso.hom h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unit comparison respects pullback composition.
Source: Stacks Project, Definition 6.26.1(2), Tag 0095; Lemma 6.26.2, Tag 0096.
(blueprint: lem-sc-picard-unit-composition)

Proof: First prove the inverse ordinary unit-composition equation. Both maps
start at O_Z, so unit_hom_ext reduces it to evaluation at 1 on the top open.
pullbackSection_one_eq identifies the inverse unit isomorphism at 1 with the
pullback of 1. pullbackSection_pullbackSection identifies its image under the
inverse composition comparison with the twice-pulled section. Naturality of
the unit at the inverse unit comparison for l identifies the other route with
this same section. Equality of inverse maps of isomorphisms gives the forward
ordinary equation. Finally expand the Picard unit and composition isomorphisms.
Naturality of picardTensorComparison k moves the unit map for l across that
comparison. Apply the ordinary equation, then cancel the inverse and hom of
the comparison at k followed by l. These section and adjunction identities
include zero rings, empty schemes and identity morphisms. -/
theorem picardTensorUnitIso_comp
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) :
    (tensorPullback k).map (picardTensorUnitIso l).hom ≫
      (picardTensorUnitIso k).hom =
    (picardTensorCompIso k l (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (picardTensorUnitIso (k ≫ l)).hom := by
  simp only [picardTensorUnitIso, picardTensorCompIso, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  erw [(picardTensorComparison k).hom.naturality_assoc]
  rw [pullbackUnitIso_comp]
  simp only [Iso.app_hom, Iso.symm_hom, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.Scheme.Modules
