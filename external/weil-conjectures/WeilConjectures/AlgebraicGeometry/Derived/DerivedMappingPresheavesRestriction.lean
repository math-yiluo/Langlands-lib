/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Restriction of derived mapping presheaves -/

@[expose] public section

universe u
open CategoryTheory Limits AlgebraicGeometry.Scheme
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem triangle_assoc
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    [Abelian C] [Abelian D] [Abelian E] [Abelian A]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory A]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ A) (P : C ⥤ E) (Q : D ⥤ A) (R : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive] [P.Additive] [Q.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : P ≅ F ⋙ G) (e' : Q ≅ G ⋙ H) (a : R ≅ F ⋙ Q) (b : R ≅ P ⋙ H)
    (h : a ≪≫ isoWhiskerLeft F e' = b ≪≫ isoWhiskerRight e H)
    (K : DerivedCategory C) :
    (mapDerivedCategoryTriangleIso a).hom.app K ≫
        (mapDerivedCategoryTriangleIso e').hom.app (F.mapDerivedCategory.obj K) =
      (mapDerivedCategoryTriangleIso b).hom.app K ≫
        H.mapDerivedCategory.map ((mapDerivedCategoryTriangleIso e).hom.app K) := by
  have hm : (mapDerivedCategoryNatIso a).hom.app K ≫
      (mapDerivedCategoryNatIso (isoWhiskerLeft F e')).hom.app K =
      (mapDerivedCategoryNatIso b).hom.app K ≫
        (mapDerivedCategoryNatIso (isoWhiskerRight e H)).hom.app K := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app,
      ← mapDerivedCategoryNatIso_trans, ← mapDerivedCategoryNatIso_trans, h]
  have hWL := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft F e') K
  have hWR := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight e H) K
  have hA := congr_app (mapDerivedCategoryCompIso_assoc F G H) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hWL
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hWR
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hA
  simp only [mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hWL, reassoc_of% hm, hA, reassoc_of% hWR]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def dcomp (B : Type (u + 1)) [CommRing B]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :=
  Functor.mapDerivedCategoryTriangleIso
    (upperStarComp (ModuleCat.{u + 1} B) f g fg hfg)

private theorem dcomp_assoc
    (B : Type (u + 1)) [CommRing B]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (dcomp B f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
        (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map
          ((dcomp B g h gh hgh).hom.app K) =
      (dcomp B fg h fgh hfgh).hom.app K ≫
        (dcomp B f g fg hfg).hom.app
          ((upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.obj K) := by
  let A := ModuleCat.{u + 1} B
  have hc : upperStarComp A fg h fgh hfgh ≪≫
      Functor.isoWhiskerLeft (upperStar A h) (upperStarComp A f g fg hfg) =
      upperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc]) ≪≫
        Functor.isoWhiskerRight (upperStarComp A g h gh hgh) (upperStar A f) := by
    apply Iso.ext
    exact (upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh).symm
  exact (Functor.triangle_assoc (upperStar A h) (upperStar A g) (upperStar A f)
    (upperStar A gh) (upperStar A fg) (upperStar A fgh)
    (upperStarComp A g h gh hgh) (upperStarComp A f g fg hfg)
    (upperStarComp A fg h fgh hfgh)
    (upperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])) hc K).symm

private theorem restriction_coherence
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (U : X.Etale) {V W : U.left.Etale} (g : V ⟶ W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj V).hom K).hom ≫
      (derivedMapRestrictionIso B g
        ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K)).hom =
    (derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).map g).left K).hom ≫
      (upperStar (ModuleCat.{u + 1} B) g.left).mapDerivedCategory.map
        ((derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj W).hom K).hom) := by
  change (dcomp B V.hom U.hom (V.hom ≫ U.hom) rfl).hom.app K ≫
      (dcomp B g.left W.hom V.hom g.w.symm).hom.app
        ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K) =
    (dcomp B g.left (W.hom ≫ U.hom) (V.hom ≫ U.hom)
      ((congrArg (fun k ↦ k ≫ U.hom) g.w.symm).trans
        (Category.assoc g.left W.hom U.hom))).hom.app K ≫
      (upperStar (ModuleCat.{u + 1} B) g.left).mapDerivedCategory.map
        ((dcomp B W.hom U.hom (W.hom ≫ U.hom) rfl).hom.app K)
  exact (dcomp_assoc B g.left W.hom U.hom V.hom (W.hom ≫ U.hom) (V.hom ≫ U.hom)
    g.w.symm rfl rfl K).symm

private theorem conjugation_natural
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {KV LV KV' LV' : D} {KW LW KW' LW' : C}
    (rV : KV ≅ KV') (sV : LV ≅ LV') (rW : KW ≅ KW') (sW : LW ≅ LW')
    (cK : KV ≅ H.obj KW) (cL : LV ≅ H.obj LW)
    (dK : KV' ≅ H.obj KW') (dL : LV' ≅ H.obj LW')
    (hK : rV.hom ≫ dK.hom = cK.hom ≫ H.map rW.hom)
    (hL : sV.hom ≫ dL.hom = cL.hom ≫ H.map sW.hom) (a : KW ⟶ LW) :
    rV.inv ≫ cK.hom ≫ H.map a ≫ cL.inv ≫ sV.hom =
      dK.hom ≫ H.map (rW.inv ≫ a ≫ sW.hom) ≫ dL.inv := by
  have hk : rV.inv ≫ cK.hom = dK.hom ≫ H.map rW.inv := by
    apply (cancel_mono (H.map rW.hom)).mp
    have hh := congrArg (fun k ↦ rV.inv ≫ k) hK.symm
    calc
      (rV.inv ≫ cK.hom) ≫ H.map rW.hom = dK.hom := by
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh
      _ = (dK.hom ≫ H.map rW.inv) ≫ H.map rW.hom := by
        rw [Category.assoc, ← H.map_comp, rW.inv_hom_id, H.map_id, Category.comp_id]
  have hl : cL.inv ≫ sV.hom = H.map sW.hom ≫ dL.inv := by
    apply (cancel_epi cL.hom).mp
    have hh := congrArg (fun k ↦ k ≫ dL.inv) hL.symm
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc,
      Category.comp_id] using hh.symm
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc rV.inv cK.hom, hk]
  simp only [Category.assoc]
  rw [hl]

/-- The derived mapping presheaves commute with localization of the etale site.

Source: Stacks Project, Tag 09BE, lemma-locally-constant-map, restriction of derived maps.
(blueprint: lem-weil-pbc-derived-mapping-presheaves-restriction)

Proof: An object V of U.left's small etale site corresponds to the etale X-scheme
with structure map V.hom followed by U.hom. The derived pullback composition
isomorphism identifies K restricted to this X-scheme with V.hom's pullback of
K restricted to U. Conjugation by this isomorphism and the corresponding one for L
gives the required bijection of Hom sets; the same conjugation of isomorphisms gives
the bijection of Isom sets. These bijections are inverse to conjugation by the inverse
comparisons. For an arrow V to W over U.left, the two naturality composites agree by
associativity of pullback: the underived upperStarComp associativity law lifts along
Functor.mapDerivedCategoryNatIso, using mapDerivedCategoryCompIso's associativity
and its naturality in each exact functor. Cancelling the middle comparison and its
inverse gives the naturality equations for both presheaves. No finiteness, boundedness
or nonemptiness assumption enters this argument. -/
theorem derived_mapping_presheaves_restriction
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.Etale) :
    Nonempty
      ((Scheme.Etale.etaleToOver U).op ⋙ (Over.forget U).op ⋙ derivedHomPresheaf B K L ≅
        derivedHomPresheaf B
          ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K)
          ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L)) ∧
    Nonempty
      ((Scheme.Etale.etaleToOver U).op ⋙ (Over.forget U).op ⋙ derivedIsoPresheaf B K L ≅
        derivedIsoPresheaf B
          ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K)
          ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L)) := by
  constructor
  · refine ⟨NatIso.ofComponents (fun V ↦
      (Iso.homCongr (derivedMapRestrictionIso B
        ((Scheme.Etale.etaleToOver U).obj V.unop).hom K)
          (derivedMapRestrictionIso B
            ((Scheme.Etale.etaleToOver U).obj V.unop).hom L)).toIso) ?_⟩
    intro V W g
    ext a
    let H := (upperStar (ModuleCat.{u + 1} B) g.unop.left).mapDerivedCategory
    let rV := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj W.unop).hom K
    let sV := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj W.unop).hom L
    let rW := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj V.unop).hom K
    let sW := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj V.unop).hom L
    let cK := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).map g.unop).left K
    let cL := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).map g.unop).left L
    let dK := derivedMapRestrictionIso B g.unop
      ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K)
    let dL := derivedMapRestrictionIso B g.unop
      ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L)
    change rV.inv ≫ (cK.hom ≫ H.map a ≫ cL.inv) ≫ sV.hom =
      dK.hom ≫ H.map (rW.inv ≫ a ≫ sW.hom) ≫ dL.inv
    simpa only [Category.assoc] using
      conjugation_natural H rV sV rW sW cK cL dK dL
        (restriction_coherence X B U g.unop K) (restriction_coherence X B U g.unop L) a
  · refine ⟨NatIso.ofComponents (fun V ↦
      (Iso.isoCongr (derivedMapRestrictionIso B
        ((Scheme.Etale.etaleToOver U).obj V.unop).hom K)
          (derivedMapRestrictionIso B
            ((Scheme.Etale.etaleToOver U).obj V.unop).hom L)).toIso) ?_⟩
    intro V W g
    ext a
    apply Iso.ext
    let H := (upperStar (ModuleCat.{u + 1} B) g.unop.left).mapDerivedCategory
    let rV := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj W.unop).hom K
    let sV := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj W.unop).hom L
    let rW := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj V.unop).hom K
    let sW := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).obj V.unop).hom L
    let cK := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).map g.unop).left K
    let cL := derivedMapRestrictionIso B ((Scheme.Etale.etaleToOver U).map g.unop).left L
    let dK := derivedMapRestrictionIso B g.unop
      ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K)
    let dL := derivedMapRestrictionIso B g.unop
      ((upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L)
    change rV.inv ≫ (cK.hom ≫ H.map a.hom ≫ cL.inv) ≫ sV.hom =
      dK.hom ≫ H.map (rW.inv ≫ a.hom ≫ sW.hom) ≫ dL.inv
    simpa only [Category.assoc] using
      conjugation_natural H rV sV rW sW cK cL dK dL
        (restriction_coherence X B U g.unop K) (restriction_coherence X B U g.unop L) a.hom

end AlgebraicGeometry.Etale
