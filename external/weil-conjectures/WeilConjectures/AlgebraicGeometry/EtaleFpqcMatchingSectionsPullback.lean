/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition

/-! # Propagation of matching global sections to an arbitrary cone
Source: Stacks Project, Tag 09XN, paragraph beginning "Let V";
Sites Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-etale-fpqc-matching-sections-pullback). -/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem mp_heq {A B : Sort (u + 1)} (e : A = B) (x : A) :
    HEq (Eq.mp e x) x := by
  cases e
  rfl

private theorem eq_mp_of_heq {A B : Sort (u + 1)} (e : B = A)
    (x : A) (y : B) (h : HEq x y) : x = Eq.mp e y := by
  cases e
  exact eq_of_heq h

private abbrev sections {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :=
  F.obj.obj (op (Scheme.Etale.mk (𝟙 S)))

private noncomputable def sectionPull {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    sections G → sections ((Scheme.etaleSetPullback a).obj G) :=
  fun s ↦ ((Scheme.etaleSetPullback a).obj G).obj.map
    (MorphismProperty.Over.homMk
      (pullback.lift a (𝟙 Z) ((Category.comp_id _).trans (Category.id_comp _).symm))
      (by simp) : Scheme.Etale.mk (𝟙 Z) ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ a).obj (Scheme.Etale.mk (𝟙 Y))).op
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ a) (Type (u + 1))
      (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit.app
        G).hom.app (op (Scheme.Etale.mk (𝟙 Y))) s)

private noncomputable def sectionCompare {S Y Z : Scheme.{u}} (g : Y ⟶ S)
    (a : Z ⟶ Y) (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    sections ((Scheme.etaleSetPullback g).obj F) →
      sections ((Scheme.etaleSetPullback (a ≫ g)).obj F) :=
  fun s ↦ ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
    S Y Z g a).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
    (sectionPull a ((Scheme.etaleSetPullback g).obj F) s)

private theorem sectionCompare_congr {S Y Z : Scheme.{u}} (g g' : Y ⟶ S)
    (a a' : Z ⟶ Y) (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : sections ((Scheme.etaleSetPullback g).obj F))
    (s' : sections ((Scheme.etaleSetPullback g').obj F))
    (hg : g = g') (ha : a = a') (hs : HEq s s') :
    HEq (sectionCompare g a F s) (sectionCompare g' a' F s') := by
  subst g' a'
  cases hs
  rfl

private noncomputable abbrev L {S Y : Scheme.{u}} (g : Y ⟶ S) :=
  Scheme.etaleSetPullback g

private noncomputable abbrev B {Y Z : Scheme.{u}} (a : Z ⟶ Y) :=
  MorphismProperty.Over.pullback @Etale ⊤ a

private noncomputable abbrev sectionUnit {Y Z : Scheme.{u}} (a : Z ⟶ Y) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (B a) (Type (u + 1))
    (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit

private noncomputable def terminalIso {S Y : Scheme.{u}} (g : Y ⟶ S) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk (𝟙 S)) ≅
      Scheme.Etale.mk (𝟙 Y) :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) g)) (Category.comp_id _)

private noncomputable def sectionIso {S Y : Scheme.{u}} (g : Y ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :=
  ((Scheme.etaleSetPullback g).obj F).obj.mapIso (terminalIso g).op

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- Identify terminal sections with sections on the base change of the base terminal object.
private theorem sectionCompare_bridge {S Y Z : Scheme.{u}} (g : Y ⟶ S)
    (a : Z ⟶ Y) (k : Z ⟶ S) (hk : a ≫ g = k)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : sections ((Scheme.etaleSetPullback g).obj F)) :
    (sectionIso k F).hom (Eq.mp (congrArg
      (fun f ↦ sections ((Scheme.etaleSetPullback f).obj F)) hk) (sectionCompare g a F s)) =
      etaleSetSectionComparison a g k hk F (Scheme.Etale.mk (𝟙 S))
        ((sectionIso g F).hom s) := by
  subst k
  let O := Scheme.Etale.mk (𝟙 S)
  let U := Scheme.Etale.mk (𝟙 Y)
  let V := Scheme.Etale.mk (𝟙 Z)
  let G := (L g).obj F
  let E := (L a).obj G
  let K := (L (a ≫ g)).obj F
  let α := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 S Y Z g a).hom.app F
  let d : V ⟶ (B a).obj U := MorphismProperty.Over.homMk
    (pullback.lift a (𝟙 Z) ((Category.comp_id _).trans (Category.id_comp _).symm))
    (by simp [V])
  let p := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) a g).hom.app O
  have hn := ((sectionUnit a).app G).hom.naturality (terminalIso g).hom.op
  have hc := α.hom.naturality (terminalIso (a ≫ g)).hom.op
  have hp := α.hom.naturality p.op
  change E.obj.map (terminalIso (a ≫ g)).hom.op ≫
      α.hom.app (op ((B (a ≫ g)).obj O)) =
    α.hom.app (op V) ≫ K.obj.map (terminalIso (a ≫ g)).hom.op at hc
  change E.obj.map p.op ≫ α.hom.app (op ((B (a ≫ g)).obj O)) =
    α.hom.app (op ((B a).obj ((B g).obj O))) ≫ K.obj.map p.op at hp
  have hd : (terminalIso (a ≫ g)).hom ≫ d = p ≫ (B a).map (terminalIso g).hom := by
    apply MorphismProperty.Over.Hom.ext
    change (terminalIso (a ≫ g)).hom.left ≫ d.left =
      p.left ≫ ((B a).map (terminalIso g).hom).left
    apply pullback.hom_ext <;>
      simp [d, p, terminalIso, MorphismProperty.Over.pullback, O, U, Category.assoc]
  have he : ((sectionUnit a).app G).hom.app (op U) ≫ E.obj.map d.op ≫
      α.hom.app (op V) ≫ K.obj.map (terminalIso (a ≫ g)).hom.op =
    G.obj.map (terminalIso g).hom.op ≫
      ((sectionUnit a).app G).hom.app (op ((B g).obj O)) ≫
      α.hom.app (op ((B a).obj ((B g).obj O))) ≫ K.obj.map p.op := by
    change G.obj.map (terminalIso g).hom.op ≫
      ((sectionUnit a).app G).hom.app (op ((B g).obj O)) =
      ((sectionUnit a).app G).hom.app (op U) ≫
        E.obj.map ((B a).map (terminalIso g).hom).op at hn
    rw [← hc, ← hp, reassoc_of% hn]
    simp only [← Functor.map_comp_assoc, ← op_comp, hd]
  simp only [sectionIso, sectionCompare, sectionPull, etaleSetSectionComparison,
    Functor.mapIso_hom, Iso.op_hom, eqToHom_refl, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, Category.id_comp, comp_apply, Eq.mp]
  convert ConcreteCategory.congr_hom he s using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- Conjugate the existing section-comparison composition law by the terminal isomorphisms.
private theorem sectionCompare_comp {S Y W Z : Scheme.{u}} (g : Y ⟶ S)
    (a : W ⟶ Y) (h : Z ⟶ W) (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : sections ((L g).obj F)) :
    HEq (sectionCompare (a ≫ g) h F (sectionCompare g a F s))
      (sectionCompare g (h ≫ a) F s) := by
  let k := (h ≫ a) ≫ g
  have hk : h ≫ (a ≫ g) = k := (Category.assoc h a g).symm
  let e := congrArg (fun f ↦ sections ((L f).obj F)) hk
  let t := sectionCompare (a ≫ g) h F (sectionCompare g a F s)
  have h₁ := sectionCompare_bridge (a ≫ g) h k hk F (sectionCompare g a F s)
  have h₂ := sectionCompare_bridge g a (a ≫ g) rfl F s
  have h₃ := sectionCompare_bridge g (h ≫ a) k rfl F s
  have h₄ := ConcreteCategory.congr_hom
    (etaleSetSectionComparisonComposition a h g (a ≫ g) k rfl hk F
      (Scheme.Etale.mk (𝟙 S))) ((sectionIso g F).hom s)
  have ht : (sectionIso k F).hom (Eq.mp e t) =
      (sectionIso k F).hom (sectionCompare g (h ≫ a) F s) :=
    h₁.trans ((congrArg
      (fun x ↦ etaleSetSectionComparison h (a ≫ g) k hk F (Scheme.Etale.mk (𝟙 S)) x)
        h₂).trans (h₄.trans h₃.symm))
  exact (mp_heq e t).symm.trans
    (heq_of_eq ((sectionIso k F).toEquiv.injective ht))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Tag 09XN, paragraph beginning "Let V";
Sites Tags 03CB and 03CC for composition units.
(blueprint: lem-weil-pbc-etale-fpqc-matching-sections-pullback).

Proof: The equality a ≫ g_j = b ≫ g_k defines l = (a,b) from Z to
T_j ×_S T_k. Pull the given overlap equality back along l and restrict to the
identity étale object of Z. The unit is natural in the sheaf morphisms given by
the composition isomorphisms and in the site morphisms given by the terminal
restriction maps. Their associativity equation identifies the two successive
composition maps with composition along l ≫ pr_j and l ≫ pr_k. The composition
unit equation combines the two unit maps, and the presheaf functor law combines
the restrictions. The resulting maps to the fibre products have first projections
a and b and second projection id_Z, hence equal the displayed maps by pullback
uniqueness. The equations l ≫ pr_j = a and l ≫ pr_k = b identify the results with
the stated expressions; equality elimination gives precisely the transport along
hab. No covering, open, or representative is used. Empty Z gives the unique
sections; the same formulas hold when j = k or a and b are identities. -/
theorem etaleFpqcMatchingSections_pullback
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : ∀ i, ((Scheme.etaleSetPullback (g i)).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (T i)))))
    (hcompat : ∀ i j,
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S (T i) (pullback (g i) (g j)) (g i) (pullback.fst (g i) (g j))).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
        (((Scheme.etaleSetPullback (pullback.fst (g i) (g j))).obj
            ((Scheme.etaleSetPullback (g i)).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst (g i) (g j)) (𝟙 (pullback (g i) (g j)))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))).obj
                (Scheme.Etale.mk (𝟙 (T i)))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))) _
            ((T i).smallGrothendieckTopology @Etale)
            ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (g i)).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 (T i)))) (s i))) =
        Eq.mp (congrArg (fun k : pullback (g i) (g j) ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j))))))
          (pullback.condition (f := g i) (g := g j)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S (T j) (pullback (g i) (g j)) (g j) (pullback.snd (g i) (g j))).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
          (((Scheme.etaleSetPullback (pullback.snd (g i) (g j))).obj
              ((Scheme.etaleSetPullback (g j)).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd (g i) (g j)) (𝟙 (pullback (g i) (g j)))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))).obj
                  (Scheme.Etale.mk (𝟙 (T j)))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))) _
              ((T j).smallGrothendieckTopology @Etale)
              ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback (g j)).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 (T j)))) (s j))))) :
    ∀ (j k : I) (Z : Scheme.{u}) (a : Z ⟶ T j) (b : Z ⟶ T k)
      (hab : a ≫ g j = b ≫ g k),
      let Ga := (Scheme.etaleSetPullback (g j)).obj F
      let Gb := (Scheme.etaleSetPullback (g k)).obj F
      let Oa := Scheme.Etale.mk (𝟙 (T j))
      let Ob := Scheme.Etale.mk (𝟙 (T k))
      let δa : Scheme.Etale.mk (𝟙 Z) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ a).obj Oa :=
        MorphismProperty.Over.homMk
          (pullback.lift a (𝟙 Z) ((Category.comp_id _).trans (Category.id_comp _).symm))
          (by simp)
      let δb : Scheme.Etale.mk (𝟙 Z) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ b).obj Ob :=
        MorphismProperty.Over.homMk
          (pullback.lift b (𝟙 Z) ((Category.comp_id _).trans (Category.id_comp _).symm))
          (by simp)
      let ηa := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ a) (Type (u + 1))
        ((T j).smallGrothendieckTopology @Etale)
        (Z.smallGrothendieckTopology @Etale)).unit.app Ga).hom.app (op Oa)
      let ηb := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ b) (Type (u + 1))
        ((T k).smallGrothendieckTopology @Etale)
        (Z.smallGrothendieckTopology @Etale)).unit.app Gb).hom.app (op Ob)
      let ca := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        S (T j) Z (g j) a).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
      let cb := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        S (T k) Z (g k) b).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
      ca (((Scheme.etaleSetPullback a).obj Ga).obj.map δa.op (ηa (s j))) =
        Eq.mp (congrArg (fun f : Z ⟶ S ↦ ((Scheme.etaleSetPullback f).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 Z)))) hab.symm)
          (cb (((Scheme.etaleSetPullback b).obj Gb).obj.map δb.op (ηb (s k)))) := by
  intro j k Z a b hab
  change sectionCompare (g j) a F (s j) =
    Eq.mp _ (sectionCompare (g k) b F (s k))
  apply eq_mp_of_heq
  let l := pullback.lift a b hab
  have hj : l ≫ pullback.fst (g j) (g k) = a := pullback.lift_fst _ _ _
  have hk : l ≫ pullback.snd (g j) (g k) = b := pullback.lift_snd _ _ _
  have hov : HEq
      (sectionCompare (g j) (pullback.fst (g j) (g k)) F (s j))
      (sectionCompare (g k) (pullback.snd (g j) (g k)) F (s k)) :=
    (heq_of_eq (hcompat j k)).trans (mp_heq _ _)
  have hmap := sectionCompare_congr
    (pullback.fst (g j) (g k) ≫ g j) (pullback.snd (g j) (g k) ≫ g k)
    l l F _ _ (pullback.condition) rfl hov
  exact (sectionCompare_congr (g j) (g j) a
    (l ≫ pullback.fst (g j) (g k)) F _ _ rfl hj.symm (HEq.refl _)).trans
    ((sectionCompare_comp (g j) (pullback.fst (g j) (g k)) l F (s j)).symm.trans
      (hmap.trans ((sectionCompare_comp (g k) (pullback.snd (g j) (g k)) l F (s k)).trans
        (sectionCompare_congr (g k) (g k) (l ≫ pullback.snd (g j) (g k))
          b F _ _ rfl hk (HEq.refl _)))))

end AlgebraicGeometry
