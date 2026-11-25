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

private lemma coefficient_comp {Yi Yj Yk Zi Zj Zk : Scheme.{v}}
    (a : Zj ⟶ Zi) (b : Zk ⟶ Zj) (c : Zk ⟶ Zi)
    (d : Yj ⟶ Yi) (e : Yk ⟶ Yj) (t : Yk ⟶ Yi)
    (ri : Yi ⟶ Zi) (rj : Yj ⟶ Zj) (rk : Yk ⟶ Zk)
    (hc : c = b ≫ a) (ht : t = e ≫ d)
    (hd : d ≫ ri = rj ≫ a) (he : e ≫ rj = rk ≫ b)
    (htc : t ≫ ri = rk ≫ c)
    (Fi : Sheaf Zi.smallEtaleTopology AddCommGrpCat.{v + 1})
    (Fj : Sheaf Zj.smallEtaleTopology AddCommGrpCat.{v + 1})
    (Fk : Sheaf Zk.smallEtaleTopology AddCommGrpCat.{v + 1})
    (α : (upperStar AddCommGrpCat.{v + 1} a).obj Fi ⟶ Fj)
    (β : (upperStar AddCommGrpCat.{v + 1} b).obj Fj ⟶ Fk)
    (γ : (upperStar AddCommGrpCat.{v + 1} c).obj Fi ⟶ Fk)
    (hγ : HEq γ ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app Fi ≫
      (upperStar AddCommGrpCat.{v + 1} b).map α ≫ β)) :
    (upperStarComp AddCommGrpCat.{v + 1} t ri).inv.app Fi ≫
        (upperStarComp AddCommGrpCat.{v + 1} rk c (t ≫ ri) htc).hom.app Fi ≫
        (upperStar AddCommGrpCat.{v + 1} rk).map γ =
      (upperStarComp AddCommGrpCat.{v + 1} e d t ht).hom.app
        ((upperStar AddCommGrpCat.{v + 1} ri).obj Fi) ≫
      (upperStar AddCommGrpCat.{v + 1} e).map
        ((upperStarComp AddCommGrpCat.{v + 1} d ri).inv.app Fi ≫
          (upperStarComp AddCommGrpCat.{v + 1} rj a (d ≫ ri) hd).hom.app Fi ≫
          (upperStar AddCommGrpCat.{v + 1} rj).map α) ≫
      (upperStarComp AddCommGrpCat.{v + 1} e rj).inv.app Fj ≫
        (upperStarComp AddCommGrpCat.{v + 1} rk b (e ≫ rj) he).hom.app Fj ≫
        (upperStar AddCommGrpCat.{v + 1} rk).map β := by
  subst c
  have hγ' := eq_of_heq hγ
  let Bi := (upperStarComp AddCommGrpCat.{v + 1} rk (b ≫ a) (t ≫ ri) htc).symm ≪≫
    upperStarComp AddCommGrpCat.{v + 1} t ri
  let Bj := (upperStarComp AddCommGrpCat.{v + 1} rk b (e ≫ rj) he).symm ≪≫
    upperStarComp AddCommGrpCat.{v + 1} e rj
  let Bd := (upperStarComp AddCommGrpCat.{v + 1} rj a (d ≫ ri) hd).symm ≪≫
    upperStarComp AddCommGrpCat.{v + 1} d ri
  have key : (upperStar AddCommGrpCat.{v + 1} rk).map
      ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app Fi) ≫
      Bj.hom.app ((upperStar AddCommGrpCat.{v + 1} a).obj Fi) =
    Bi.hom.app Fi ≫
      (upperStarComp AddCommGrpCat.{v + 1} e d t ht).hom.app
        ((upperStar AddCommGrpCat.{v + 1} ri).obj Fi) ≫
      (upperStar AddCommGrpCat.{v + 1} e).map (Bd.inv.app Fi) := by
    simpa only [Bi, Bj, Bd, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc] using
      square_triangle rk (b ≫ a) b a t e d ri rj rfl ht htc he hd Fi
  have key' : Bi.inv.app Fi ≫ (upperStar AddCommGrpCat.{v + 1} rk).map
      ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app Fi) =
    (upperStarComp AddCommGrpCat.{v + 1} e d t ht).hom.app
      ((upperStar AddCommGrpCat.{v + 1} ri).obj Fi) ≫
    (upperStar AddCommGrpCat.{v + 1} e).map (Bd.inv.app Fi) ≫
      Bj.inv.app ((upperStar AddCommGrpCat.{v + 1} a).obj Fi) := by
    apply (cancel_epi (Bi.hom.app Fi)).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% key]
    simp only [Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  change Bi.inv.app Fi ≫ (upperStar AddCommGrpCat.{v + 1} rk).map γ =
    (upperStarComp AddCommGrpCat.{v + 1} e d t ht).hom.app
      ((upperStar AddCommGrpCat.{v + 1} ri).obj Fi) ≫
    (upperStar AddCommGrpCat.{v + 1} e).map
      (Bd.inv.app Fi ≫ (upperStar AddCommGrpCat.{v + 1} rj).map α) ≫
    Bj.inv.app Fj ≫ (upperStar AddCommGrpCat.{v + 1} rk).map β
  rw [hγ']
  simp only [Functor.map_comp, Category.assoc]
  have hn : (upperStar AddCommGrpCat.{v + 1} e).map
      ((upperStar AddCommGrpCat.{v + 1} rj).map α) ≫ Bj.inv.app Fj =
    Bj.inv.app ((upperStar AddCommGrpCat.{v + 1} a).obj Fi) ≫
      (upperStar AddCommGrpCat.{v + 1} rk).map
        ((upperStar AddCommGrpCat.{v + 1} b).map α) := Bj.inv.naturality α
  rw [reassoc_of% hn, reassoc_of% key']

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

private lemma single_transition_comp {A B C : Type*}
    [Category A] [Category B] [Category C] [Abelian A] [Abelian B] [Abelian C]
    (P : B ⥤ C) (Q : A ⥤ B) (T : A ⥤ C)
    [P.Additive] [Q.Additive] [T.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : T ≅ Q ⋙ P) (Xi : A) (Xj : B) (Xk : C)
    (α : Q.obj Xi ⟶ Xj) (β : P.obj Xj ⟶ Xk) (γ : T.obj Xi ⟶ Xk)
    (hγ : γ = e.hom.app Xi ≫ P.map α ≫ β) :
    (T.mapCochainComplexSingleFunctor 0).hom.app Xi ≫
        (CochainComplex.singleFunctor C 0).map γ =
      (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor A 0).obj Xi) ≫
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Q.mapCochainComplexSingleFunctor 0).hom.app Xi ≫
          (CochainComplex.singleFunctor B 0).map α) ≫
      (P.mapCochainComplexSingleFunctor 0).hom.app Xj ≫
        (CochainComplex.singleFunctor C 0).map β := by
  have key := single_comp P Q T e Xi
  apply (cancel_epi ((T.mapCochainComplexSingleFunctor 0).inv.app Xi)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% key]
  have hn : (P.mapCochainComplexSingleFunctor 0).inv.app (Q.obj Xi) ≫
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor B 0).map α) =
    (CochainComplex.singleFunctor C 0).map (P.map α) ≫
      (P.mapCochainComplexSingleFunctor 0).inv.app Xj
    := ((P.mapCochainComplexSingleFunctor 0).inv.naturality α).symm
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hγ]
  simp only [Functor.map_comp]

/-- Composition law for restricted single transitions.
Source: Stacks Project, Tags 09Z1 and 03CB, inverse-image coherence in restriction.
(blueprint: lem-sbc-restricted-affine-single-composition-law).

Proof: Expand all three transitions. Their pullback second-projection equations give
two adjacent commuting squares and their outer rectangle. Substitute D.map_comp
and hφcomp into the outer restricted coefficient. Horizontal pasting for
squareUpperStarIso expresses the outer inverse comparison as upperStarComp for
the restricted arrows followed by the pulled-back first inverse square comparison
and the second inverse square comparison. Use naturality of the second comparison
to move the first coefficient map past it. Cancel each comparison with its inverse;
the result is the coefficient composition law on the restricted sheaves, with the
transport along restrictedAffineDiagram.map_comp. Apply HomologicalComplex.hom_ext.
In degree zero, the evaluation isomorphisms singleObjXSelf and their naturality
identify the single-complex comparison maps with this sheaf calculation; cancel
the intervening evaluation isomorphisms. In every other degree the source single
complex is zero. No directedness, cone, nonemptiness, affineness or nonzero sheaf
assumption is used, so the empty and zero cases satisfy the same equation. -/
theorem restrictedAffineSingleTransition_composition_law {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (U : S.Etale) :
    let D' := restrictedAffineDiagram D U
    let K := restrictedAffineK D F U
    let ψ := fun {i j : Iᵒᵖ} (f : j ⟶ i) ↦ restrictedAffineSingleTransition D F φ U f
    ( ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g) := by
  intro D' K ψ i j k f g
  let a := (D.map f).left
  let b := (D.map g).left
  let c := (D.map (g ≫ f)).left
  let d := D'.map f
  let e := D'.map g
  let t := D'.map (g ≫ f)
  let ri := pullback.snd U.hom (D.obj i).hom
  let rj := pullback.snd U.hom (D.obj j).hom
  let rk := pullback.snd U.hom (D.obj k).hom
  have hc : c = b ≫ a := by simp only [c, b, a, D.map_comp, Over.comp_left]
  have ht : t = e ≫ d := D'.map_comp g f
  have hd : d ≫ ri = rj ≫ a := by
    simp [d, ri, rj, a, D', restrictedAffineDiagram, rawAffineRestrictedMap]
  have he : e ≫ rj = rk ≫ b := by
    simp [e, rj, rk, b, D', restrictedAffineDiagram, rawAffineRestrictedMap]
  have htc : t ≫ ri = rk ≫ c := by
    simp [t, ri, rk, c, D', restrictedAffineDiagram, rawAffineRestrictedMap]
  let α := rawAffineRestrictedCoefficient a (D.obj i).hom (D.obj j).hom
    (Over.w (D.map f)) (F i.unop) (F j.unop) (φ f.unop) U
  let β := rawAffineRestrictedCoefficient b (D.obj j).hom (D.obj k).hom
    (Over.w (D.map g)) (F j.unop) (F k.unop) (φ g.unop) U
  let γ := rawAffineRestrictedCoefficient c (D.obj i).hom (D.obj k).hom
    (Over.w (D.map (g ≫ f))) (F i.unop) (F k.unop) (φ (g ≫ f).unop) U
  have hcoeff : γ =
      (upperStarComp AddCommGrpCat.{v + 1} e d t ht).hom.app
        ((upperStar AddCommGrpCat.{v + 1} ri).obj (F i.unop)) ≫
      (upperStar AddCommGrpCat.{v + 1} e).map α ≫ β := by
    have key := coefficient_comp a b c d e t ri rj rk hc ht hd he htc
      (F i.unop) (F j.unop) (F k.unop) (φ f.unop) (φ g.unop) (φ (g ≫ f).unop)
      (hφcomp f.unop g.unop)
    simpa only [α, β, γ, d, e, t, ri, rj, rk, D', restrictedAffineDiagram,
      rawAffineRestrictedCoefficient, Category.assoc] using key
  exact single_transition_comp
    (upperStar AddCommGrpCat.{v + 1} e) (upperStar AddCommGrpCat.{v + 1} d)
    (upperStar AddCommGrpCat.{v + 1} t)
    (upperStarComp AddCommGrpCat.{v + 1} e d t ht)
    ((upperStar AddCommGrpCat.{v + 1} ri).obj (F i.unop))
    ((upperStar AddCommGrpCat.{v + 1} rj).obj (F j.unop))
    ((upperStar AddCommGrpCat.{v + 1} rk).obj (F k.unop)) α β γ hcoeff

end AlgebraicGeometry.Etale
