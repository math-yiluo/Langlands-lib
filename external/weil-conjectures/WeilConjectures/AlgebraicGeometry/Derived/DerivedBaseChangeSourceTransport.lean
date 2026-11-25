/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontalMate

/-! # Source and apex transport of a derived base-change mate

Source: Stacks Project, Tags 08HY and 0D5T.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

private theorem transport_mate_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') (P : C ⥤ C') (Q : D ⥤ D')
    (e : P ⋙ L' ≅ L ⋙ Q) (K : C) (T : C') (q : P.obj K ⟶ T) :
    P.map (a.unit.app K) ≫
        a'.homEquiv _ _ (e.hom.app (R.obj (L.obj K)) ≫ Q.map (a.counit.app (L.obj K))) ≫
        R'.map (e.inv.app K ≫ L'.map q) = q ≫ a'.unit.app T := by
  rw [← a'.homEquiv_naturality_right, ← a'.homEquiv_naturality_left]
  have ht : L'.map (P.map (a.unit.app K)) ≫
      (e.hom.app (R.obj (L.obj K)) ≫ Q.map (a.counit.app (L.obj K))) ≫
      (e.inv.app K ≫ L'.map q) = L'.map q := by
    simp only [← Category.assoc]
    have hn := e.hom.naturality (a.unit.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn]
    simp only [Category.assoc, ← Q.map_comp_assoc, a.left_triangle_components,
      Functor.id_obj, Functor.comp_obj, Q.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  rw [ht, Adjunction.homEquiv_unit, a'.unit_naturality]

private theorem transport_mate_naturality
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (P : C ⥤ C') (Q : D ⥤ D')
    (e : P ⋙ L' ≅ L ⋙ Q) {Y Z : D} (f : Y ⟶ Z) :
    P.map (R.map f) ≫
        adj'.homEquiv _ _ (e.hom.app (R.obj Z) ≫ Q.map (adj.counit.app Z)) =
      adj'.homEquiv _ _ (e.hom.app (R.obj Y) ≫ Q.map (adj.counit.app Y)) ≫
        R'.map (Q.map f) := by
  rw [← adj'.homEquiv_naturality_left, ← adj'.homEquiv_naturality_right]
  apply congrArg (adj'.homEquiv _ _)
  have hn := e.hom.naturality (R.map f)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Q.map_comp]
  have hc := adj.counit.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]

private theorem transport_baseChange_naturality
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (r : X' ⟶ X)
    (h : r ≫ f = f' ≫ g) {K L : schemeDerivedCategory X} (a : K ⟶ L) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map a) ≫
        schemeDerivedBaseChangeMap f f' g r h L =
      schemeDerivedBaseChangeMap f f' g r h K ≫
        (schemeDerivedDirectImage f').map ((derivedPullback r).map a) := by
  let e := relativeMVComp f' g ≪≫
    eqToIso (congrArg (fun t ↦ derivedPullback t) h.symm) ≪≫ (relativeMVComp r f).symm
  have hn := transport_mate_naturality (relativeMVAdj f) (relativeMVAdj f')
    (derivedPullback g) (derivedPullback r) e a
  simpa only [schemeDerivedBaseChangeMap, relativeMVAdj, relativeMVComp, e,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Functor.comp_obj, Functor.id_obj, Category.assoc] using hn

/-- Horizontal transport of the base-change mate, with arbitrary coefficient maps.
Source: Stacks Project, Tags 08HY and 0D5T.
(blueprint: lem-pc-derived-base-change-source-transport)

Proof: Eliminate hs to make s' = k ≫ s. Put c = C(k,r), transport by hr,
then C(r',j).inv, and q0 = c.inv.app K followed by Lk(q). Transpose the inner
square mate under the k adjunction. Naturality of c and the j triangle identity
prove Lr(unit_j) followed by that mate and Rk(q0) equals q followed by unit_k.
This elementary mate-unit calculation is proved separately in this file.
The coefficient hypothesis, after precomposition by c.inv, gives
q0 followed by d = Lr'(a) followed by q'. Apply coefficient naturality to the
outer p square and unit_j. The horizontal mate-pasting theorem identifies the
result with base change for j ≫ p followed by the inverse image composition
comparison for k,s. Naturality of that image comparison moves q0 through it;
the inverse and forward comparison cancel. Substitute the coefficient equation,
then apply coefficient naturality once more to a. Functoriality and associativity
now give exactly the displayed equation. No invertibility or cartesianness is
used, so identity morphisms, empty schemes and zero objects are included. -/
theorem derivedBaseChange_source_transport
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {Y Y' B A P P' : Scheme.{u}}
    (p : Y ⟶ B) (g : A ⟶ B) (j : Y' ⟶ Y)
    (r : P ⟶ Y) (s : P ⟶ A) (r' : P' ⟶ Y') (s' : P' ⟶ A) (k : P' ⟶ P)
    (h : r ≫ p = s ≫ g) (h' : r' ≫ (j ≫ p) = s' ≫ g)
    (hr : k ≫ r = r' ≫ j) (hs : k ≫ s = s')
    (K : schemeDerivedCategory Y) (K' : schemeDerivedCategory Y')
    (T : schemeDerivedCategory P) (T' : schemeDerivedCategory P')
    (a : (derivedPullback j).obj K ⟶ K')
    (q : (derivedPullback r).obj K ⟶ T)
    (q' : (derivedPullback r').obj K' ⟶ T')
    (d : (derivedPullback k).obj T ⟶ T')
    (hq : (derivedPullback k).map q ≫ d =
      (relativeMVComp k r).hom.app K ≫
        eqToHom (congrArg (fun f ↦ (derivedPullback f).obj K) hr) ≫
        (relativeMVComp r' j).inv.app K ≫ (derivedPullback r').map a ≫ q') :
    let e := (schemeDerivedDirectImage p).map ((relativeMVAdj j).unit.app K) ≫
      (relativeMVImageComp j p).hom.app ((derivedPullback j).obj K) ≫
      (schemeDerivedDirectImage (j ≫ p)).map a
    let F := (schemeDerivedDirectImage s).map ((relativeMVAdj k).unit.app T) ≫
      (relativeMVImageComp k s).hom.app ((derivedPullback k).obj T) ≫
      eqToHom (congrArg (fun f ↦ (schemeDerivedDirectImage f).obj
        ((derivedPullback k).obj T)) hs) ≫ (schemeDerivedDirectImage s').map d
    schemeDerivedBaseChangeMap p s g r h K ≫ (schemeDerivedDirectImage s).map q ≫ F =
      (derivedPullback g).map e ≫ schemeDerivedBaseChangeMap (j ≫ p) s' g r' h' K' ≫
        (schemeDerivedDirectImage s').map q' := by
  classical
  subst s'
  let c := relativeMVComp k r ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) hr) ≪≫ (relativeMVComp r' j).symm
  let q0 := c.inv.app K ≫ (derivedPullback k).map q
  have hu : (derivedPullback r).map ((relativeMVAdj j).unit.app K) ≫
      schemeDerivedBaseChangeMap j k r r' hr.symm ((derivedPullback j).obj K) ≫
      (schemeDerivedDirectImage k).map q0 = q ≫ (relativeMVAdj k).unit.app T := by
    simpa only [schemeDerivedBaseChangeMap, relativeMVAdj, relativeMVComp,
      c, q0, Functor.comp_obj, Functor.id_obj, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
      eqToIso.hom, eqToIso.inv, eqToHom_app, Iso.symm_hom, Iso.symm_inv,
      Category.assoc] using
      transport_mate_unit (relativeMVAdj j) (relativeMVAdj k)
        (derivedPullback r) (derivedPullback r') c K T q
  have hd : q0 ≫ d = (derivedPullback r').map a ≫ q' := by
    have hq' : (derivedPullback k).map q ≫ d =
        c.hom.app K ≫ (derivedPullback r').map a ≫ q' := by
      simpa only [c, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
        eqToHom_app, Iso.symm_hom, Category.assoc] using hq
    dsimp only [q0]
    rw [Category.assoc, hq', Iso.inv_hom_id_app_assoc]
  have hn := transport_baseChange_naturality p s g r h
    ((relativeMVAdj j).unit.app K)
  have hm := schemeDerivedBaseChange_horizontal_mate j p k s g r r' h hr.symm
    ((derivedPullback j).obj K)
  have ha := transport_baseChange_naturality (j ≫ p) (k ≫ s) g r' h' a
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn ha
  have hi := (relativeMVImageComp k s).hom.naturality q0
  dsimp only [Functor.comp_map, Functor.comp_obj] at hi
  dsimp only
  simp only [eqToHom_refl, Category.id_comp, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc (schemeDerivedDirectImage s) q
    ((relativeMVAdj k).unit.app T), ← hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, reassoc_of% hm]
  rw [reassoc_of% hi]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp (schemeDerivedDirectImage (k ≫ s)) q0 d, hd]
  simp only [Functor.map_comp]
  rw [← reassoc_of% ha]

end AlgebraicGeometry
