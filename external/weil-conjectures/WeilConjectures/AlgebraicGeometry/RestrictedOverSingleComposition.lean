/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedOverSingleData

/-! # Triangle composition of restricted fixed-coefficient single complexes

Source: Stacks Project, Tags 09Z1 and 0EZM, restriction of fixed coefficients.
(blueprint: lem-sbc-restricted-over-single-composition).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar upperStarComp upperStarId

set_option backward.isDefEq.respectTransparency true in
private lemma comp_hom_assoc {X Y Z V : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fg : X ⟶ Z) (gh : Y ⟶ V) (fgh : X ⟶ V)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = f ≫ gh)
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} f gh fgh hfgh).hom.app F ≫
      (upperStar AddCommGrpCat.{u + 1} f).map
        ((upperStarComp AddCommGrpCat.{u + 1} g h gh hgh).hom.app F) =
      (upperStarComp AddCommGrpCat.{u + 1} fg h fgh
        (by rw [hfgh, hgh, hfg, Category.assoc])).hom.app F ≫
      (upperStarComp AddCommGrpCat.{u + 1} f g fg hfg).hom.app
        ((upperStar AddCommGrpCat.{u + 1} h).obj F) := by
  subst fg
  subst gh
  subst fgh
  have e := congrArg Iso.hom (upperStarComp_assoc AddCommGrpCat.{u + 1} f g h)
  simpa using NatTrans.congr_app e F

set_option backward.isDefEq.respectTransparency true in
private lemma square_triangle {X T Yi Yj Zi Zj : Scheme.{u}}
    (r : X ⟶ T) (ci : T ⟶ Zi) (cj : T ⟶ Zj) (a : Zj ⟶ Zi)
    (qi : X ⟶ Yi) (qj : X ⟶ Yj) (d : Yj ⟶ Yi)
    (ri : Yi ⟶ Zi) (rj : Yj ⟶ Zj)
    (hci : ci = cj ≫ a) (hqi : qi = qj ≫ d)
    (hi : qi ≫ ri = r ≫ ci) (hj : qj ≫ rj = r ≫ cj)
    (hd : d ≫ ri = rj ≫ a)
    (F : Sheaf Zi.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStar AddCommGrpCat.{u + 1} r).map
        ((upperStarComp AddCommGrpCat.{u + 1} cj a ci hci).hom.app F) ≫
      (upperStarComp AddCommGrpCat.{u + 1} r cj (qj ≫ rj) hj).inv.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj F) ≫
      (upperStarComp AddCommGrpCat.{u + 1} qj rj).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj F) =
      (upperStarComp AddCommGrpCat.{u + 1} r ci (qi ≫ ri) hi).inv.app F ≫
      (upperStarComp AddCommGrpCat.{u + 1} qi ri).hom.app F ≫
      (upperStarComp AddCommGrpCat.{u + 1} qj d qi hqi).hom.app
        ((upperStar AddCommGrpCat.{u + 1} ri).obj F) ≫
      (upperStar AddCommGrpCat.{u + 1} qj).map
        ((upperStarComp AddCommGrpCat.{u + 1} d ri).inv.app F) ≫
      (upperStar AddCommGrpCat.{u + 1} qj).map
        ((upperStarComp AddCommGrpCat.{u + 1} rj a (d ≫ ri) hd).hom.app F) := by
  have htot' : qi ≫ ri = qj ≫ (d ≫ ri) := by rw [hqi, Category.assoc]
  have h₁ := comp_hom_assoc r cj a (qj ≫ rj) ci (qi ≫ ri) hj hci hi F
  have h₂ := comp_hom_assoc qj d ri qi (d ≫ ri) (qi ≫ ri) hqi rfl htot' F
  have h₃ := comp_hom_assoc qj rj a (qj ≫ rj) (d ≫ ri) (qi ≫ ri)
    rfl hd htot' F
  apply (cancel_epi
    ((upperStarComp AddCommGrpCat.{u + 1} r ci (qi ≫ ri) hi).hom.app F)).1
  simp only [← Category.assoc]
  rw [h₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Category.assoc]
  rw [← h₂]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Category.id_comp]
  exact h₃.symm

set_option backward.isDefEq.respectTransparency true in
private lemma square_coefficient {X T Yi Yj Zi Zj : Scheme.{u}}
    (r : X ⟶ T) (ci : T ⟶ Zi) (cj : T ⟶ Zj) (a : Zj ⟶ Zi)
    (qi : X ⟶ Yi) (qj : X ⟶ Yj) (d : Yj ⟶ Yi)
    (ri : Yi ⟶ Zi) (rj : Yj ⟶ Zj)
    (hci : ci = cj ≫ a) (hqi : qi = qj ≫ d)
    (hi : qi ≫ ri = r ≫ ci) (hj : qj ≫ rj = r ≫ cj)
    (hd : d ≫ ri = rj ≫ a)
    (Fi : Sheaf Zi.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Fj : Sheaf Zj.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Hi Hj : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ei : Hi ≅ (upperStar AddCommGrpCat.{u + 1} ci).obj Fi)
    (ej : Hj ≅ (upperStar AddCommGrpCat.{u + 1} cj).obj Fj)
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj Fi ⟶ Fj)
    (h : Hi ⟶ Hj)
    (hh : h = ei.hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} cj a ci hci).hom.app Fi ≫
      (upperStar AddCommGrpCat.{u + 1} cj).map φ ≫ ej.inv) :
    let bi := (upperStarComp AddCommGrpCat.{u + 1} r ci (qi ≫ ri) hi).symm ≪≫
      upperStarComp AddCommGrpCat.{u + 1} qi ri
    let bj := (upperStarComp AddCommGrpCat.{u + 1} r cj (qj ≫ rj) hj).symm ≪≫
      upperStarComp AddCommGrpCat.{u + 1} qj rj
    let Ei := (upperStar AddCommGrpCat.{u + 1} r).mapIso ei ≪≫ bi.app Fi
    let Ej := (upperStar AddCommGrpCat.{u + 1} r).mapIso ej ≪≫ bj.app Fj
    let t := (upperStarComp AddCommGrpCat.{u + 1} d ri).inv.app Fi ≫
      (upperStarComp AddCommGrpCat.{u + 1} rj a (d ≫ ri) hd).hom.app Fi ≫
      (upperStar AddCommGrpCat.{u + 1} rj).map φ
    (upperStar AddCommGrpCat.{u + 1} r).map h = Ei.hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} qj d qi hqi).hom.app
        ((upperStar AddCommGrpCat.{u + 1} ri).obj Fi) ≫
      (upperStar AddCommGrpCat.{u + 1} qj).map t ≫ Ej.inv := by
  intro bi bj Ei Ej t
  apply (cancel_mono Ej.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [Ei, Ej]
  rw [hh]
  simp only [Functor.map_comp, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [Category.comp_id, Functor.map_comp, Category.assoc]
  rw [show (upperStar AddCommGrpCat.{u + 1} r).map
      ((upperStar AddCommGrpCat.{u + 1} cj).map φ) ≫ bj.hom.app Fj =
      bj.hom.app ((upperStar AddCommGrpCat.{u + 1} a).obj Fi) ≫
        (upperStar AddCommGrpCat.{u + 1} qj).map
          ((upperStar AddCommGrpCat.{u + 1} rj).map φ)
    from bj.hom.naturality φ]
  have key := square_triangle r ci cj a qi qj d ri rj hci hqi hi hj hd Fi
  dsimp only [bi, bj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at key ⊢
  simp only [Category.assoc]
  rw [reassoc_of% key]
  dsimp only [t]
  simp only [Functor.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma single_map_zero {D : Type*} [Category D] [Preadditive D]
    [HasZeroObject D] {X Y : D} (f : X ⟶ Y) :
    ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  change 𝟙 X ≫ f ≫ 𝟙 Y = f
  simp only [Category.comp_id, Category.id_comp]

private lemma inverse_eq_of_triangle {D : Type*} [Category D] {X Y : D}
    (e : X ≅ Y) (m : Y ⟶ X) (h : 𝟙 X = e.hom ≫ m) : e.inv = m := by
  simpa only [Category.comp_id] using (Iso.inv_comp_eq e).mpr h

attribute [local irreducible] rawAffineRestrictedMap restrictedOverSingleIso

set_option backward.isDefEq.respectTransparency true in
private lemma restricted_single_iso_hom {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    (restrictedOverSingleIso k F f U).hom =
      ((upperStar AddCommGrpCat.{u + 1}
        (rawAffineRestrictedMap f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) U)).mapCochainComplexSingleFunctor 0).hom.app
        ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom (B.hom ≫ k))).obj
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj F)) ≫
      (CochainComplex.singleFunctor _ 0).map
        (rawAffineRestrictedCoefficient f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w])
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj F)
          ((upperStar AddCommGrpCat.{u + 1} A.hom).obj F)
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app F) U) := by
  simp only [restrictedOverSingleIso.eq_1, asIso_hom]

set_option backward.isDefEq.respectTransparency true in
/-- Composition law for a triangle of fixed-coefficient restricted single complexes.
Source: Stacks Project, Tags 09Z1 and 0EZM, canonical fixed-coefficient comparisons.
(blueprint: lem-sbc-restricted-over-single-composition).

Proof: Substitute ha to replace the third arrow by g followed by f. Expand the
three explicit transition homs. The second pullback projections satisfy the
commuting triangles with f.left, g.left, and their composite. Apply the associativity
law of upperStarComp to these triangles and to the structure arrows to W. Naturality
moves each sheaf comparison across inverse image, and the inverse comparisons
cancel. Thus the composite of the two coefficient maps is the coefficient map
for the composite, preceded by upperStarComp for the restricted maps. Applying
the single functor and naturality of mapCochainComplexSingleFunctor gives the stated
complex identity. Its composition compatibility is checked in degree zero, where
it is the original functor composition identity; in other degrees the source is
zero. Transport along hq identifies the composite restricted map with that for a.
No cone, limiting property, or category structure on an indexing type is required;
zero sheaves, empty schemes and identity arrows satisfy the same calculation. -/
theorem restrictedOverSingle_composition {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A B C : Over W} (f : B ⟶ A) (g : C ⟶ B) (a : C ⟶ A)
    (ha : a = g ≫ f) (U : S.Etale)
    (hq : rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U =
      rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U ≫
      rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U) :
    (restrictedOverSingleIso k F a U).hom =
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1}
          (rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U)
          (rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U)
          (rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U) hq)
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F A U) ≫
      ((upperStar AddCommGrpCat.{u + 1}
        (rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (restrictedOverSingleIso k F f U).hom ≫
      (restrictedOverSingleIso k F g U).hom := by
  let qf := rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) U
  let qg := rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) U
  let qa := rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) U
  let rA := pullback.snd U.hom (A.hom ≫ k)
  let rB := pullback.snd U.hom (B.hom ≫ k)
  let rC := pullback.snd U.hom (C.hom ≫ k)
  let FA := (upperStar AddCommGrpCat.{u + 1} A.hom).obj F
  let FB := (upperStar AddCommGrpCat.{u + 1} B.hom).obj F
  let FC := (upperStar AddCommGrpCat.{u + 1} C.hom).obj F
  let ef := (upperStarComp AddCommGrpCat.{u + 1} f.left A.hom B.hom
    (Over.w f).symm).app F
  let eg := (upperStarComp AddCommGrpCat.{u + 1} g.left B.hom C.hom
    (Over.w g).symm).app F
  let ea := (upperStarComp AddCommGrpCat.{u + 1} a.left A.hom C.hom
    (Over.w a).symm).app F
  have hleft : a.left = g.left ≫ f.left := by rw [ha]; rfl
  have hA : qa ≫ rA = rC ≫ a.left := by
    set_option backward.isDefEq.respectTransparency false in
    simp [qa, rA, rC, rawAffineRestrictedMap]
  have hB : qg ≫ rB = rC ≫ g.left := by
    set_option backward.isDefEq.respectTransparency false in
    simp [qg, rB, rC, rawAffineRestrictedMap]
  have hf : qf ≫ rA = rB ≫ f.left := by
    set_option backward.isDefEq.respectTransparency false in
    simp [qf, rA, rB, rawAffineRestrictedMap]
  have he : (𝟙 FC) = ea.hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} g.left f.left a.left hleft).hom.app FA ≫
      (upperStar AddCommGrpCat.{u + 1} g.left).map ef.inv ≫ eg.inv := by
    have key := comp_hom_assoc g.left f.left A.hom a.left B.hom C.hom
      hleft (Over.w f).symm (Over.w g).symm F
    dsimp only [ef, eg, ea, FA, FC, Iso.app_hom, Iso.app_inv]
    apply (cancel_mono
      ((upperStarComp AddCommGrpCat.{u + 1} g.left B.hom C.hom
        (Over.w g).symm).hom.app F)).1
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
    rw [← reassoc_of% key]
    simp only [Functor.comp_obj, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  have key := square_coefficient rC a.left g.left f.left qa qg qf rA rB
    hleft hq hA hB hf FA FB FC FC ea eg ef.inv (𝟙 FC) he
  dsimp only at key
  rw [CategoryTheory.Functor.map_id] at key
  let Ei := (upperStar AddCommGrpCat.{u + 1} rC).mapIso ea ≪≫
    ((upperStarComp AddCommGrpCat.{u + 1} rC a.left (qa ≫ rA) hA).app FA).symm ≪≫
    (upperStarComp AddCommGrpCat.{u + 1} qa rA).app FA
  let Ej := (upperStar AddCommGrpCat.{u + 1} rC).mapIso eg ≪≫
    ((upperStarComp AddCommGrpCat.{u + 1} rC g.left (qg ≫ rB) hB).app FB).symm ≪≫
    (upperStarComp AddCommGrpCat.{u + 1} qg rB).app FB
  let tf := rawAffineRestrictedCoefficient f.left (A.hom ≫ k) (B.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) FA FB ef.inv U
  have ht : (𝟙 ((upperStar AddCommGrpCat.{u + 1} rC).obj FC)) = Ei.hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} qg qf qa hq).hom.app
        ((upperStar AddCommGrpCat.{u + 1} rA).obj FA) ≫
      (upperStar AddCommGrpCat.{u + 1} qg).map tf ≫ Ej.inv := by
    simpa only [Ei, Ej, tf, rawAffineRestrictedCoefficient, qf, rA, rB,
      CategoryTheory.Functor.map_id, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Category.assoc,
      Functor.map_comp] using key
  have hcoef := inverse_eq_of_triangle Ei _ ht
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.isDefEq.respectTransparency false in
    simp only [restricted_single_iso_hom, HomologicalComplex.comp_f,
      Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      Functor.mapHomologicalComplex_map_f, NatIso.mapHomologicalComplex_hom_app_f]
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.isDefEq.respectTransparency false in
    simp only [single_map_zero, restrictedOverSingle,
      CochainComplex.singleFunctor,
      HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      CategoryTheory.Functor.map_id, Category.id_comp]
    let ta := rawAffineRestrictedCoefficient a.left (A.hom ≫ k) (C.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) FA FC ea.inv U
    let tg := rawAffineRestrictedCoefficient g.left (B.hom ≫ k) (C.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) FB FC eg.inv U
    set_option backward.isDefEq.respectTransparency false in
    change 𝟙 _ ≫ ta =
      (upperStarComp AddCommGrpCat.{u + 1} qg qf qa hq).hom.app
        ((upperStar AddCommGrpCat.{u + 1} rA).obj FA) ≫
      (upperStar AddCommGrpCat.{u + 1} qg).map (𝟙 _ ≫ tf) ≫ 𝟙 _ ≫ tg
    simp only [Category.id_comp]
    simpa only [ta, tg, Ei, Ej, tf, qa, qf, qg, rA, rB, rC, FA, FB, FC, ea, eg, ef,
      rawAffineRestrictedCoefficient, Iso.trans_inv, Iso.symm_inv, Iso.app_hom,
      Iso.app_inv, Functor.mapIso_inv, Functor.comp_obj, Category.assoc] using hcoef
  · exact (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0
      ((upperStar AddCommGrpCat.{u + 1} rC).obj FC) n hn).eq_of_tgt _ _

end AlgebraicGeometry.Etale
