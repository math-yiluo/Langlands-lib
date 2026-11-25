/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleMaps

/-! # Explicit maps for restricted degree-zero complexes

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private lemma comp_hom_assoc {X Y Z V : Scheme.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fg : X ⟶ Z) (gh : Y ⟶ V) (fgh : X ⟶ V)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = f ≫ gh)
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (upperStarComp AddCommGrpCat.{v + 1} f gh fgh hfgh).hom.app F ≫
      (upperStar AddCommGrpCat.{v + 1} f).map
        ((upperStarComp AddCommGrpCat.{v + 1} g h gh hgh).hom.app F) =
      (upperStarComp AddCommGrpCat.{v + 1} fg h fgh
        (by rw [hfgh, hgh, hfg, Category.assoc])).hom.app F ≫
      (upperStarComp AddCommGrpCat.{v + 1} f g fg hfg).hom.app
        ((upperStar AddCommGrpCat.{v + 1} h).obj F) := by
  subst fg
  subst gh
  subst fgh
  have e := congrArg Iso.hom (upperStarComp_assoc AddCommGrpCat.{v + 1} f g h)
  simpa using NatTrans.congr_app e F

private lemma square_triangle {X T Yi Yj Zi Zj : Scheme.{v}}
    (r : X ⟶ T) (ci : T ⟶ Zi) (cj : T ⟶ Zj) (a : Zj ⟶ Zi)
    (qi : X ⟶ Yi) (qj : X ⟶ Yj) (d : Yj ⟶ Yi)
    (ri : Yi ⟶ Zi) (rj : Yj ⟶ Zj)
    (hci : ci = cj ≫ a) (hqi : qi = qj ≫ d)
    (hi : qi ≫ ri = r ≫ ci) (hj : qj ≫ rj = r ≫ cj)
    (hd : d ≫ ri = rj ≫ a)
    (F : Sheaf Zi.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (upperStar AddCommGrpCat.{v + 1} r).map
        ((upperStarComp AddCommGrpCat.{v + 1} cj a ci hci).hom.app F) ≫
      (upperStarComp AddCommGrpCat.{v + 1} r cj (qj ≫ rj) hj).inv.app
        ((upperStar AddCommGrpCat.{v + 1} a).obj F) ≫
      (upperStarComp AddCommGrpCat.{v + 1} qj rj).hom.app
        ((upperStar AddCommGrpCat.{v + 1} a).obj F) =
      (upperStarComp AddCommGrpCat.{v + 1} r ci (qi ≫ ri) hi).inv.app F ≫
      (upperStarComp AddCommGrpCat.{v + 1} qi ri).hom.app F ≫
      (upperStarComp AddCommGrpCat.{v + 1} qj d qi hqi).hom.app
        ((upperStar AddCommGrpCat.{v + 1} ri).obj F) ≫
      (upperStar AddCommGrpCat.{v + 1} qj).map
        ((upperStarComp AddCommGrpCat.{v + 1} d ri).inv.app F) ≫
      (upperStar AddCommGrpCat.{v + 1} qj).map
        ((upperStarComp AddCommGrpCat.{v + 1} rj a (d ≫ ri) hd).hom.app F) := by
  have htot' : qi ≫ ri = qj ≫ (d ≫ ri) := by rw [hqi, Category.assoc]
  have h₁ := comp_hom_assoc r cj a (qj ≫ rj) ci (qi ≫ ri) hj hci hi F
  have h₂ := comp_hom_assoc qj d ri qi (d ≫ ri) (qi ≫ ri) hqi rfl htot' F
  have h₃ := comp_hom_assoc qj rj a (qj ≫ rj) (d ≫ ri) (qi ≫ ri)
    rfl hd htot' F
  apply (cancel_epi
    ((upperStarComp AddCommGrpCat.{v + 1} r ci (qi ≫ ri) hi).hom.app F)).1
  simp only [← Category.assoc]
  rw [h₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Category.assoc]
  rw [← h₂]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Category.id_comp]
  exact h₃.symm

private lemma square_coefficient {X T Yi Yj Zi Zj : Scheme.{v}}
    (r : X ⟶ T) (ci : T ⟶ Zi) (cj : T ⟶ Zj) (a : Zj ⟶ Zi)
    (qi : X ⟶ Yi) (qj : X ⟶ Yj) (d : Yj ⟶ Yi)
    (ri : Yi ⟶ Zi) (rj : Yj ⟶ Zj)
    (hci : ci = cj ≫ a) (hqi : qi = qj ≫ d)
    (hi : qi ≫ ri = r ≫ ci) (hj : qj ≫ rj = r ≫ cj)
    (hd : d ≫ ri = rj ≫ a)
    (Fi : Sheaf Zi.smallEtaleTopology AddCommGrpCat.{v + 1})
    (Fj : Sheaf Zj.smallEtaleTopology AddCommGrpCat.{v + 1})
    (Hi Hj : Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1})
    (ei : Hi ≅ (upperStar AddCommGrpCat.{v + 1} ci).obj Fi)
    (ej : Hj ≅ (upperStar AddCommGrpCat.{v + 1} cj).obj Fj)
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj Fi ⟶ Fj)
    (h : Hi ⟶ Hj)
    (hh : h = ei.hom ≫
      (upperStarComp AddCommGrpCat.{v + 1} cj a ci hci).hom.app Fi ≫
      (upperStar AddCommGrpCat.{v + 1} cj).map φ ≫ ej.inv) :
    let bi := (upperStarComp AddCommGrpCat.{v + 1} r ci (qi ≫ ri) hi).symm ≪≫
      upperStarComp AddCommGrpCat.{v + 1} qi ri
    let bj := (upperStarComp AddCommGrpCat.{v + 1} r cj (qj ≫ rj) hj).symm ≪≫
      upperStarComp AddCommGrpCat.{v + 1} qj rj
    let Ei := (upperStar AddCommGrpCat.{v + 1} r).mapIso ei ≪≫ bi.app Fi
    let Ej := (upperStar AddCommGrpCat.{v + 1} r).mapIso ej ≪≫ bj.app Fj
    let t := (upperStarComp AddCommGrpCat.{v + 1} d ri).inv.app Fi ≫
      (upperStarComp AddCommGrpCat.{v + 1} rj a (d ≫ ri) hd).hom.app Fi ≫
      (upperStar AddCommGrpCat.{v + 1} rj).map φ
    (upperStar AddCommGrpCat.{v + 1} r).map h = Ei.hom ≫
      (upperStarComp AddCommGrpCat.{v + 1} qj d qi hqi).hom.app
        ((upperStar AddCommGrpCat.{v + 1} ri).obj Fi) ≫
      (upperStar AddCommGrpCat.{v + 1} qj).map t ≫ Ej.inv := by
  intro bi bj Ei Ej t
  apply (cancel_mono Ej.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [Ei, Ej]
  rw [hh]
  simp only [Functor.map_comp, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [Category.comp_id, Functor.map_comp, Category.assoc]
  rw [show (upperStar AddCommGrpCat.{v + 1} r).map
      ((upperStar AddCommGrpCat.{v + 1} cj).map φ) ≫ bj.hom.app Fj =
      bj.hom.app ((upperStar AddCommGrpCat.{v + 1} a).obj Fi) ≫
        (upperStar AddCommGrpCat.{v + 1} qj).map
          ((upperStar AddCommGrpCat.{v + 1} rj).map φ)
    from bj.hom.naturality φ]
  have key := square_triangle r ci cj a qi qj d ri rj hci hqi hi hj hd Fi
  dsimp only [bi, bj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at key ⊢
  simp only [Category.assoc]
  rw [reassoc_of% key]
  dsimp only [t]
  simp only [Functor.map_comp]

private lemma single_comp {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (P : B ⥤ C) (Q : A ⥤ B) (T : A ⥤ C)
    [P.Additive] [Q.Additive] [T.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : T ≅ Q ⋙ P) (X : A) :
    (CochainComplex.singleFunctor C 0).map (e.hom.app X) ≫
        (P.mapCochainComplexSingleFunctor 0).inv.app (Q.obj X) =
      (T.mapCochainComplexSingleFunctor 0).inv.app X ≫
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
          ((CochainComplex.singleFunctor A 0).obj X) ≫
        (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Q.mapCochainComplexSingleFunctor 0).hom.app X) := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f,
      Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      Functor.mapHomologicalComplex_map_f, NatIso.mapHomologicalComplex_hom_app_f]
    rw [show ((CochainComplex.singleFunctor C 0).map (e.hom.app X)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (T.obj X)).hom ≫
        e.hom.app X ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (P.obj (Q.obj X))).inv
      from HomologicalComplex.single_map_f_self _ 0 _]
    rw [Category.assoc, Category.assoc]
    simp only [Iso.inv_hom_id_assoc, Functor.map_comp, Category.assoc]
    dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    rw [e.hom.naturality_assoc
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv]
    simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    have hc : Q.map (𝟙 X) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Q.obj X)).inv =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Q.obj X)).inv := by
      simp only [Q.map_id, Category.id_comp]
    exact congrArg (fun k ↦
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (T.obj X)).hom ≫
        e.hom.app X) ≫ P.map k) hc.symm
  · exact (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0 (T.obj X) n hn).eq_of_src _ _

private lemma single_naturality {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (P : B ⥤ C) (Q : A ⥤ B) (T : A ⥤ C)
    [P.Additive] [Q.Additive] [T.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : T ≅ Q ⋙ P) (Xi : A) (Xj : B) (Hi Hj : C)
    (ai : Hi ≅ T.obj Xi) (aj : Hj ≅ P.obj Xj) (φ : Q.obj Xi ⟶ Xj) (h : Hi ⟶ Hj)
    (hh : h = ai.hom ≫ e.hom.app Xi ≫ P.map φ ≫ aj.inv) :
    let ei := (CochainComplex.singleFunctor C 0).mapIso ai ≪≫
      ((T.mapCochainComplexSingleFunctor 0).app Xi).symm
    let ej := (CochainComplex.singleFunctor C 0).mapIso aj ≪≫
      ((P.mapCochainComplexSingleFunctor 0).app Xj).symm
    (CochainComplex.singleFunctor C 0).map h = ei.hom ≫
      (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor A 0).obj Xi) ≫
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Q.mapCochainComplexSingleFunctor 0).hom.app Xi ≫
          (CochainComplex.singleFunctor B 0).map φ) ≫ ej.inv := by
  intro ei ej
  dsimp only [ei, ej]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  have key := single_comp P Q T e Xi
  rw [← reassoc_of% key]
  have nat : (P.mapCochainComplexSingleFunctor 0).inv.app (Q.obj Xi) ≫
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor B 0).map φ) =
      (CochainComplex.singleFunctor C 0).map (P.map φ) ≫
        (P.mapCochainComplexSingleFunctor 0).inv.app Xj :=
    ((P.mapCochainComplexSingleFunctor 0).inv.naturality φ).symm
  rw [reassoc_of% nat]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hh]
  simp only [Functor.map_comp]

/-- The explicit cone comparison intertwines the restricted diagram transitions.
Source: Stacks Project, Tag 09Z1 proof (restriction to an affine etale object),
and Tag 03CB inverse-image composition comparisons.
(blueprint: lem-sbc-restricted-affine-single-cone-naturality).

Proof: Expand the explicit cone isomorphisms and restricted transitions, and substitute
hH for the coefficient diagram arrow. Write q_i for a restricted cone leg, r_i for
the stage second projection, and r for the cone point second projection. The pullback
projection identity is q_i followed by r_i equals r followed by c_i. The cone triangle
identifies q_j followed by the restricted transition with q_i. Apply upperStarComp_assoc
first to the triangle of the two original cone legs and the original transition, then
to the corresponding restricted triangle, and then to the second-projection squares.
Naturality moves the images of eH and of the coefficient transition through these
comparisons. Cancel inverse comparisons and the adjacent eH isomorphisms. Applying
singleFunctor and its natural inverse-image comparison gives the displayed equation.
This argument needs only hH, not the coefficient transition laws or any colimit. -/
theorem restrictedAffineSingleConeIso_naturality {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    (U : S.Etale) :
    let D' := restrictedAffineDiagram D U
    let c' := restrictedAffineCone D c U
    let K := restrictedAffineK D F U
    let G := restrictedAffineG D c H U
    let ψ := fun {i j : Iᵒᵖ} (f : j ⟶ i) ↦ restrictedAffineSingleTransition D F φ U f
    let eG := restrictedAffineSingleConeIso D c F H eH U
    ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv := by
  intro D' c' K G ψ eG i j f
  let qi := c'.π.app i
  let qj := c'.π.app j
  let d := D'.map f
  let ri := pullback.snd U.hom (D.obj i).hom
  let rj := pullback.snd U.hom (D.obj j).hom
  let r := pullback.snd U.hom c.pt.hom
  let ci := (c.π.app i).left
  let cj := (c.π.app j).left
  let a := (D.map f).left
  have hci : ci = cj ≫ a :=
    (congrArg (fun t ↦ t.left) (c.w f)).symm
  have hqi : qi = qj ≫ d := (c'.w f).symm
  have hi : qi ≫ ri = r ≫ ci := by
    simp [qi, ri, r, ci, c', restrictedAffineCone, rawAffineRestrictedMap]
  have hj : qj ≫ rj = r ≫ cj := by
    simp [qj, rj, r, cj, c', restrictedAffineCone, rawAffineRestrictedMap]
  have hd : d ≫ ri = rj ≫ a := by
    simp [d, ri, rj, a, D', restrictedAffineDiagram, rawAffineRestrictedMap]
  let ei := (upperStar AddCommGrpCat.{v + 1} r).mapIso (eH i.unop) ≪≫
    ((upperStarComp AddCommGrpCat.{v + 1} r ci (qi ≫ ri) hi).app (F i.unop)).symm ≪≫
    (upperStarComp AddCommGrpCat.{v + 1} qi ri).app (F i.unop)
  let ej := (upperStar AddCommGrpCat.{v + 1} r).mapIso (eH j.unop) ≪≫
    ((upperStarComp AddCommGrpCat.{v + 1} r cj (qj ≫ rj) hj).app (F j.unop)).symm ≪≫
    (upperStarComp AddCommGrpCat.{v + 1} qj rj).app (F j.unop)
  let t := rawAffineRestrictedCoefficient a (D.obj i).hom (D.obj j).hom
    (Over.w (D.map f)) (F i.unop) (F j.unop) (φ f.unop) U
  have ht : (upperStar AddCommGrpCat.{v + 1} r).map (H.map f.unop) =
      ei.hom ≫ (upperStarComp AddCommGrpCat.{v + 1} qj d qi hqi).hom.app
        ((upperStar AddCommGrpCat.{v + 1} ri).obj (F i.unop)) ≫
      (upperStar AddCommGrpCat.{v + 1} qj).map t ≫ ej.inv := by
    have key := square_coefficient r ci cj a qi qj d ri rj hci hqi hi hj hd
      (F i.unop) (F j.unop) (H.obj i.unop) (H.obj j.unop)
      (eH i.unop) (eH j.unop) (φ f.unop) (H.map f.unop) (hH f.unop)
    simpa only [ei, ej, t, d, D', restrictedAffineDiagram, ri, rj,
      rawAffineRestrictedCoefficient,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Category.assoc,
      Functor.map_comp] using key
  exact single_naturality
    (upperStar AddCommGrpCat.{v + 1} qj) (upperStar AddCommGrpCat.{v + 1} d)
    (upperStar AddCommGrpCat.{v + 1} qi)
    (upperStarComp AddCommGrpCat.{v + 1} qj d qi hqi)
    ((upperStar AddCommGrpCat.{v + 1} ri).obj (F i.unop))
    ((upperStar AddCommGrpCat.{v + 1} rj).obj (F j.unop))
    ((upperStar AddCommGrpCat.{v + 1} r).obj (H.obj i.unop))
    ((upperStar AddCommGrpCat.{v + 1} r).obj (H.obj j.unop))
    ei ej t ((upperStar AddCommGrpCat.{v + 1} r).map (H.map f.unop)) ht

end AlgebraicGeometry.Etale
