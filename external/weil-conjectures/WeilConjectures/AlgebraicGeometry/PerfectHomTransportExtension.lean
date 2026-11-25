/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent

/-! # Canonical transport of Hom groups in the base-change system.
Source: Stacks Project, Cohomology, Tag 0D5S and perfect.tex, Tag 09RE.
(blueprint: lem-pc-perfect-hom-transport).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The canonical arrow from the colimit affine scheme to a finite stage.
Source: Stacks Project, Tag 09RE, the affine limit system.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def overlapLimitArrow
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} (k : Set.Ici i) :
    Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE k.property))) :=
  Over.homMk (Spec.map (c.ι.app k.val))
    (by dsimp; rw [← Spec.map_comp, c.w (homOfLE k.property)])







/-- The conjugation formula for one named base-change arrow. -/
theorem perfectHomMap_eq {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s g f =
      (perfectHomComparison s g).hom.app P ≫
        (derivedPullback (baseChangeMap s g)).map f ≫
        (perfectHomComparison s g).inv.app Q := rfl








private theorem cc_assoc {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (perfectHomComposition f g) (derivedPullback h) ≪≫
      perfectHomComposition h (f ≫ g) =
      Functor.associator (derivedPullback g) (derivedPullback f) (derivedPullback h) ≪≫
        Functor.isoWhiskerLeft (derivedPullback g) (perfectHomComposition h f) ≪≫
          perfectHomComposition (h ≫ f) g ≪≫
          eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k) (Category.assoc h f g)) := by
  exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))).2).2.2 h f g

private noncomputable def tr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback g).obj P ⟶ (derivedPullback g).obj Q) :
    (derivedPullback (f ≫ g)).obj P ⟶ (derivedPullback (f ≫ g)).obj Q :=
  (perfectHomComposition f g).inv.app P ≫ (derivedPullback f).map a ≫
    (perfectHomComposition f g).hom.app Q

private theorem tr_assoc {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback g).obj P ⟶ (derivedPullback g).obj Q) :
    tr h (f ≫ g) (tr f g a) =
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f g))).inv.app P ≫ tr (h ≫ f) g a ≫
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f g))).hom.app Q := by
  have hi := congrArg (fun e ↦ e.inv.app P) (cc_assoc h f g)
  have hh := congrArg (fun e ↦ e.hom.app Q) (cc_assoc h f g)
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp, Category.assoc] at hi hh
  simp only [tr, Functor.map_comp]
  simp only [Category.assoc] at hi hh ⊢
  rw [← Category.assoc ((perfectHomComposition h (f ≫ g)).inv.app P)
    ((derivedPullback h).map ((perfectHomComposition f g).inv.app P)), hi]
  simp only [Category.assoc]
  rw [hh]
  have hn := (perfectHomComposition h f).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((derivedPullback h).map ((derivedPullback f).map a)), hn]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private noncomputable def trTo {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (e : f ≫ p = q) {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    (derivedPullback q).obj P ⟶ (derivedPullback q).obj Q :=
  (eqToIso (congrArg (fun k ↦ derivedPullback k) e.symm)).hom.app P ≫
    tr f p a ≫ (eqToIso (congrArg (fun k ↦ derivedPullback k) e.symm)).inv.app Q

private theorem trTo_refl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    trTo f p (f ≫ p) rfl a = tr f p a := by
  simp only [trTo, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id]

-- Comparing the fixed composition isomorphisms reduces their universal properties.
private theorem trTo_assoc {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y)
    (p : Y ⟶ Z) (q : X ⟶ Z) (r : W ⟶ Z) (eq : f ≫ p = q) (er : h ≫ q = r)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    trTo h q r er (trTo f p q eq a) =
      trTo (h ≫ f) p r (by rw [Category.assoc, eq, er]) a := by
  subst q
  subst r
  rw [trTo_refl, trTo_refl]
  have he : eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
      (Category.assoc h f p).symm) =
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f p))).symm := rfl
  conv_rhs => unfold trTo
  rw [he]
  exact tr_assoc h f p a

private theorem trTo_congr {X Y Z : Scheme.{u}} (f f' : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (e : f ≫ p = q) (e' : f' ≫ p = q) (hf : f = f')
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    trTo f p q e a = trTo f' p q e' a := by
  subst f'
  rfl

private theorem homMap_trTo {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S}
    (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s g a = trTo (baseChangeMap s g) (pullback.fst s T.hom)
      (pullback.fst s T'.hom) (baseChangeMap_fst s g) a := by
  simp only [trTo, tr, perfectHomMap, perfectHomComparison, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Category.assoc]







/-- The finite-to-colimit transport uses the fixed comparison for its
canonical arrow. This is the defining conjugation equation. -/
theorem perfectLimitMap_eq {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    (c : Cocone R) {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j : I} (hij : i ≤ j) {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :
    perfectLimitMap R c s hij f =
      (perfectHomComparison s (overlapLimitArrow R c ⟨j, hij⟩)).hom.app P ≫
        (derivedPullback (baseChangeMap s (overlapLimitArrow R c ⟨j, hij⟩))).map f ≫
        (perfectHomComparison s (overlapLimitArrow R c ⟨j, hij⟩)).inv.app Q := by
  unfold perfectLimitMap
  exact perfectHomMap_eq s (overlapLimitArrow R c ⟨j, hij⟩) f







end AlgebraicGeometry
