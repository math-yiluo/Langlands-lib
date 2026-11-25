/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueNormalizationMap

/-! # PicardOrdinaryResidueCoefficientSquare

## References

* Stacks Project, Tags 0096, 06YJ, 0A1D, 08HY, 0D5S and 01F7
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

namespace Modules

attribute [local irreducible] tensorPullback

private noncomputable def comparison {Y Z : Scheme.{v}} (a : Y ⟶ Z) :=
  (Classical.choose (exists_tensorPullbackAdjunction a)).leftAdjointUniq
    (pullbackPushforwardAdjunction a)

private theorem mate_comparison {Y Z : Scheme.{v}} (a : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction a) (coefficientTensorAdjunction a)
      (comparison a).hom = 𝟙 _ := by
  simp [comparison, coefficientTensorAdjunction, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv_symm_apply_inv]

private theorem mate_comparison_inv {Y Z : Scheme.{v}} (a : Y ⟶ Z) :
    conjugateEquiv (coefficientTensorAdjunction a) (pullbackPushforwardAdjunction a)
      (comparison a).inv = 𝟙 _ := by
  simp [comparison, coefficientTensorAdjunction, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv_symm_apply_hom]

private theorem mate_comp {A B C : Scheme.{v}} (a : A ⟶ B) (b : B ⟶ C) :
    conjugateEquiv (pullbackPushforwardAdjunction (a ≫ b))
      ((pullbackPushforwardAdjunction b).comp (pullbackPushforwardAdjunction a))
      (pullbackComp a b).hom = (pushforwardComp a b).inv := by
  have h : conjugateIsoEquiv
      ((pullbackPushforwardAdjunction b).comp (pullbackPushforwardAdjunction a))
      (pullbackPushforwardAdjunction (a ≫ b)) (pullbackComp a b).symm =
      pushforwardComp a b := by
    apply Iso.ext
    exact conjugateEquiv_pullbackComp_inv a b
  exact congrArg Iso.inv h

private theorem mate_congr {A B : Scheme.{v}} {a b : A ⟶ B} (w : a = b) :
    conjugateEquiv (pullbackPushforwardAdjunction b) (pullbackPushforwardAdjunction a)
      (pullbackCongr w).hom = (pushforwardCongr w).inv := by
  subst b
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, conjugateEquiv_id]
  ext N V
  simp

private theorem mate_associator_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
    {R : B ⥤ A} {S : C ⥤ B} {T : D ⥤ C}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ T) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
      (Functor.associator F G H).inv = (Functor.associator T S R).inv := by
  have h : conjugateIsoEquiv (a.comp (b.comp c)) ((a.comp b).comp c)
      (Functor.associator F G H) = Functor.associator T S R := by
    apply Iso.ext
    exact conjugateEquiv_associator_hom a b c
  exact congrArg Iso.inv h

private noncomputable def triangle {A B X : Scheme.{v}}
    (q : A ⟶ X) (q' : B ⟶ X) (b : B ⟶ A) (hb : b ≫ q = q') :
    tensorPullback q ⋙ pullback b ≅ tensorPullback q' :=
  Functor.isoWhiskerRight (comparison q) (pullback b) ≪≫
    pullbackComp b q ≪≫ pullbackCongr hb ≪≫ (comparison q').symm

private theorem mate_triangle {A B X : Scheme.{v}}
    (q : A ⟶ X) (q' : B ⟶ X) (b : B ⟶ A) (hb : b ≫ q = q') :
    conjugateEquiv (coefficientTensorAdjunction q')
      ((coefficientTensorAdjunction q).comp (pullbackPushforwardAdjunction b))
      (triangle q q' b hb).hom =
      (pushforwardCongr hb).inv ≫ (pushforwardComp b q).inv := by
  dsimp only [triangle, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction q'),
    ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (b ≫ q)),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction q).comp (pullbackPushforwardAdjunction b))]
  simp only [conjugateEquiv_whiskerRight, mate_comparison, mate_comparison_inv,
    mate_congr, mate_comp, Functor.whiskerLeft_id', Category.comp_id, Category.id_comp]

private noncomputable def coefficient {X X' A A' : Scheme.{v}}
    (u : X' ⟶ X) (q : A ⟶ X) (qi : A' ⟶ X') (j : A' ⟶ A)
    (h : j ≫ q = qi ≫ u) :
    tensorPullback q ⋙ pullback j ≅ tensorPullback u ⋙ tensorPullback qi :=
  Functor.isoWhiskerRight (comparison q) (pullback j) ≪≫ pullbackComp j q ≪≫
    pullbackCongr h ≪≫ (pullbackComp qi u).symm ≪≫
    Functor.isoWhiskerRight (comparison u).symm (pullback qi) ≪≫
    Functor.isoWhiskerLeft (tensorPullback u) (comparison qi).symm

private theorem mate_coefficient {X X' A A' : Scheme.{v}}
    (u : X' ⟶ X) (q : A ⟶ X) (qi : A' ⟶ X') (j : A' ⟶ A)
    (h : j ≫ q = qi ≫ u) :
    conjugateEquiv ((coefficientTensorAdjunction u).comp (coefficientTensorAdjunction qi))
      ((coefficientTensorAdjunction q).comp (pullbackPushforwardAdjunction j))
      (coefficient u q qi j h).hom =
      (pushforwardComp qi u).hom ≫ (pushforwardCongr h).inv ≫
        (pushforwardComp j q).inv := by
  dsimp only [coefficient, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv]
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp _
      ((coefficientTensorAdjunction u).comp (pullbackPushforwardAdjunction qi)),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction u).comp (pullbackPushforwardAdjunction qi)),
    ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (qi ≫ u)),
    ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (j ≫ q)),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction q).comp (pullbackPushforwardAdjunction j))]
  simp only [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    mate_comparison, mate_comparison_inv, mate_comp, mate_congr, Category.assoc,
    conjugateEquiv_pullbackComp_inv, Functor.whiskerLeft_id',
    Functor.whiskerRight_id', Category.comp_id, Category.id_comp]

private theorem restriction_path
    {C D : Type*} [Category C] [Category D] [Quiver.IsThin C] (F : C ⥤ D)
    {A B E G : C} (a : A ⟶ G) (b : A ⟶ B) (c : B ⟶ E) (d : E ⟶ G) :
    F.map a = F.map b ≫ 𝟙 _ ≫ 𝟙 _ ≫ F.map c ≫ 𝟙 _ ≫ F.map d ≫ 𝟙 _ := by
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  congr 1
  exact Subsingleton.elim _ _

-- Taking mates expands a six-functor square.
private theorem coefficient_square
    {X X' A A' B B' : Scheme.{v}} (u : X' ⟶ X)
    (q : A ⟶ X) (qi : A' ⟶ X') (qt : B ⟶ X) (qit : B' ⟶ X')
    (jW : A' ⟶ A) (j : B' ⟶ B) (b : B ⟶ A) (bi : B' ⟶ A')
    (hW : jW ≫ q = qi ≫ u) (ht : j ≫ qt = qit ≫ u)
    (hb : b ≫ q = qt) (hbi : bi ≫ qi = qit) (hr : j ≫ b = bi ≫ jW)
    (L : X.Modules) :
    (pullback j).map ((triangle q qt b hb).hom.app L) ≫
        (coefficient u qt qit j ht).hom.app L =
      (pullbackComp j b ≪≫ pullbackCongr hr ≪≫ (pullbackComp bi jW).symm).hom.app
          ((tensorPullback q).obj L) ≫
        (pullback bi).map ((coefficient u q qi jW hW).hom.app L) ≫
          (triangle qi qit bi hbi).hom.app ((tensorPullback u).obj L) := by
  let aq := coefficientTensorAdjunction q
  let aqt := coefficientTensorAdjunction qt
  let au := coefficientTensorAdjunction u
  let ai := coefficientTensorAdjunction qi
  let ait := coefficientTensorAdjunction qit
  let aj := pullbackPushforwardAdjunction j
  let ajW := pullbackPushforwardAdjunction jW
  let ab := pullbackPushforwardAdjunction b
  let abi := pullbackPushforwardAdjunction bi
  let c := pullbackComp j b ≪≫ pullbackCongr hr ≪≫ (pullbackComp bi jW).symm
  let lhs := Functor.whiskerRight (triangle q qt b hb).hom (pullback j) ≫
    (coefficient u qt qit j ht).hom
  let rhs := (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (tensorPullback q) c.hom ≫
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (coefficient u q qi jW hW).hom (pullback bi) ≫
          (Functor.associator _ _ _).hom ≫
            Functor.whiskerLeft (tensorPullback u) (triangle qi qit bi hbi).hom
  have hc : conjugateEquiv (ajW.comp abi) (ab.comp aj) c.hom =
      (pushforwardComp bi jW).hom ≫ (pushforwardCongr hr).inv ≫
        (pushforwardComp j b).inv := by
    dsimp only [c, Iso.trans_hom, Iso.symm_hom]
    simp only [← Category.assoc]
    rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (bi ≫ jW)),
      ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (j ≫ b))]
    simp only [ajW, abi, ab, aj, Category.assoc,
      conjugateEquiv_pullbackComp_inv, mate_congr, mate_comp]
  have hn : lhs = rhs := by
    apply (conjugateEquiv (au.comp ait) ((aq.comp ab).comp aj)).injective
    dsimp only [lhs, rhs]
    simp only [← Category.assoc]
    rw [← conjugateEquiv_comp _ (aqt.comp aj)]
    rw [← conjugateEquiv_comp _ (au.comp (ai.comp abi)),
      ← conjugateEquiv_comp _ ((au.comp ai).comp abi),
      ← conjugateEquiv_comp _ ((aq.comp ajW).comp abi),
      ← conjugateEquiv_comp _ (aq.comp (ajW.comp abi)),
      ← conjugateEquiv_comp _ (aq.comp (ab.comp aj))]
    simp only [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
      conjugateEquiv_associator_hom, mate_associator_inv, hc]
    dsimp only [aq, aqt, au, ai, ait, aj, ajW, ab, abi]
    simp only [mate_triangle, mate_coefficient]
    apply NatTrans.ext
    funext N
    apply hom_ext
    intro O
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
      Hom.comp_app, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
      pushforwardCongr_inv_app_app,
      pushforward_map_app, pushforward_obj_presheaf_map, Category.id_comp, Category.comp_id]
    simp only [Category.assoc, ← Functor.map_comp]
    exact restriction_path N.presheaf _ _ _ _
  have hm := congrArg (fun z ↦ z.app L) hn
  simpa only [lhs, rhs, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, c] using hm

end Modules

private theorem triangle_eq_ordinary
    {A B X : Scheme.{v}} (q : A ⟶ X) (q' : B ⟶ X) (b : B ⟶ A)
    (hb : b ≫ q = q') (L : X.Modules) :
    (Modules.triangle q q' b hb).hom.app L =
      (picardOrdinaryCoefficientTriangle q q' b hb L).hom := by
  rfl

-- Evaluating the square at L unfolds its tensor and ordinary coefficient isomorphisms.
set_option maxRecDepth 2048 in
/-- Ordinary coefficient normalization commutes with the fibre square. -/
theorem picard_ordinary_residue_coefficient_square
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)]
    [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [Modules.IsInvertible L]
    (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (g : T ⟶ W) (t : T' ⟶ S) (r : T ≅ T')
    (_h : g ≫ k = r.hom ≫ t)
    (e : pullback (pullback.snd f k) g ≅ pullback f t)
    (hefst : e.hom ≫ pullback.fst f t =
      pullback.fst (pullback.snd f k) g ≫ pullback.fst f k)
    (_hesnd : e.hom ≫ pullback.snd f t ≫ r.inv = pullback.snd (pullback.snd f k) g)
    (ei : ∀ i, pullback (pullback.snd (fi i) k) g ≅ pullback (fi i) t)
    (heifst : ∀ i, (ei i).hom ≫ pullback.fst (fi i) t =
      pullback.fst (pullback.snd (fi i) k) g ≫ pullback.fst (fi i) k)
    (_heisnd : ∀ i, (ei i).hom ≫ pullback.snd (fi i) t ≫ r.inv =
      pullback.snd (pullback.snd (fi i) k) g)
    (τ : (Modules.tensorPullback (pullback.fst f t)).obj L ≅
      SheafOfModules.unit (pullback f t).ringCatSheaf) :
    let j := fun i ↦ ((Over.pullback t).map
      (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left
    let τi := fun i ↦
      (picardResidueCoefficientIso f (fi i) (ui i) (hui i) L T' t).symm ≪≫
        (Modules.pullback (j i)).mapIso τ ≪≫ Modules.pullbackObjUnitIso (j i)
    let jW := fun i ↦ ((Over.pullback k).map
      (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left
    let b := e.inv ≫ pullback.fst (pullback.snd f k) g
    let bi := fun i ↦ (ei i).inv ≫ pullback.fst (pullback.snd (fi i) k) g
    let hb : b ≫ pullback.fst f k = pullback.fst f t := by
      dsimp only [b]
      rw [Category.assoc, ← hefst, e.inv_hom_id_assoc]
    let hbi : ∀ i, bi i ≫ pullback.fst (fi i) k = pullback.fst (fi i) t := by
      intro i
      dsimp only [bi]
      rw [Category.assoc, ← heifst, (ei i).inv_hom_id_assoc]
    let c := picardOrdinaryCoefficientTriangle
      (pullback.fst f k) (pullback.fst f t) b hb L ≪≫ τ
    let ci := fun i ↦ picardOrdinaryCoefficientTriangle
      (pullback.fst (fi i) k) (pullback.fst (fi i) t) (bi i) (hbi i)
        ((Modules.tensorPullback (ui i)).obj L) ≪≫ τi i
    ∀ (hr : ∀ i, j i ≫ b = bi i ≫ jW i), ∀ i,
      (Modules.pullback (j i)).map c.hom ≫ (Modules.pullbackObjUnitIso (j i)).hom =
      ((Modules.pullbackComp (bi i) (jW i)).app
          ((Modules.tensorPullback (pullback.fst f k)).obj L) ≪≫
        (Modules.pullbackCongr (hr i).symm).app
          ((Modules.tensorPullback (pullback.fst f k)).obj L) ≪≫
        (Modules.pullbackComp (j i) b).symm.app
          ((Modules.tensorPullback (pullback.fst f k)).obj L)).inv ≫
      (Modules.pullback (bi i)).map
        (picardResidueCoefficientIso f (fi i) (ui i) (hui i) L W k).hom ≫
      (ci i).hom := by
  classical
  intro j τi jW b bi hb hbi c ci hr i
  let α := picardResidueCoefficientIso f (fi i) (ui i) (hui i) L W k
  let αt := picardResidueCoefficientIso f (fi i) (ui i) (hui i) L T' t
  have hc := Modules.coefficient_square (ui i)
    (pullback.fst f k) (pullback.fst (fi i) k)
    (pullback.fst f t) (pullback.fst (fi i) t)
    (jW i) (j i) b (bi i)
    (picardCoefficientBaseMap_fst f (fi i) (ui i) (hui i) W k)
    (picardCoefficientBaseMap_fst f (fi i) (ui i) (hui i) T' t)
    hb (hbi i) (hr i) L
  rw [triangle_eq_ordinary] at hc
  change (Modules.pullback (j i)).map
      (picardOrdinaryCoefficientTriangle (pullback.fst f k) (pullback.fst f t) b hb L).hom ≫
        αt.hom =
      (Modules.pullbackComp (j i) b ≪≫ Modules.pullbackCongr (hr i) ≪≫
        (Modules.pullbackComp (bi i) (jW i)).symm).hom.app
          ((Modules.tensorPullback (pullback.fst f k)).obj L) ≫
        (Modules.pullback (bi i)).map α.hom ≫
          (picardOrdinaryCoefficientTriangle (pullback.fst (fi i) k)
            (pullback.fst (fi i) t) (bi i) (hbi i)
            ((Modules.tensorPullback (ui i)).obj L)).hom at hc
  have hh := congrArg (fun z ↦ z ≫ αt.inv ≫
    (Modules.pullback (j i)).map τ.hom ≫ (Modules.pullbackObjUnitIso (j i)).hom) hc
  simpa only [c, ci, τi, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc, α, αt, Modules.pullbackCongr,
    eqToIso.inv, eqToIso.hom, eqToHom_app, NatTrans.comp_app] using hh

end Scheme
end AlgebraicGeometry
