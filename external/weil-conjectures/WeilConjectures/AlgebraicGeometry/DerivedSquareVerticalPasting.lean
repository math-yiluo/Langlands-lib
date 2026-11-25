/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # Vertical coherence of derived pullback squares
Source: Stacks Project, Tag 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe v
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- Vertical pasting of canonical derived square comparisons.
Source: Stacks Project, Tag 0D5S; step 2 of
lem-sc-picard-coefficient-transpose-pasting.
(blueprint: lem-sc-derived-square-vertical-pasting)

Proof: Expand each square as composition.hom, equality transport, and
composition.inv. Postcompose with the invertible composition comparison for
b followed by a followed by p. Apply the associativity law of the selected
composition family first to p2,i,t and then to b,a,p. Naturality moves the
comparison for b,a past the remaining square. Transport the two middle
comparisons along hb and ha. The equality transports then compose to the
same map, because hab, h and the three square equations imply the same
equality of scheme morphisms; proof irrelevance identifies the proofs.
Cancel the composition comparison. This uses only pullback coherence,
not direct image, adjunction counits, coefficients or invertibility of any
single-module map. Identity arrows, zero complexes and empty schemes obey
the same natural transformation identities. -/
theorem canonicalDerivedSquareComparison_vertical
    {A B C W T T' : Scheme.{v}}
    (p : A ⟶ W) (p1 : B ⟶ T) (p2 : C ⟶ T')
    (t : T ⟶ W) (i : T' ⟶ T) (t' : T' ⟶ W)
    (a : B ⟶ A) (b : C ⟶ B) (a' : C ⟶ A)
    (ha : a ≫ p = p1 ≫ t) (hb : b ≫ p1 = p2 ≫ i)
    (ha' : a' ≫ p = p2 ≫ t') (h : i ≫ t = t') (hab : b ≫ a = a')
    (E : schemeDerivedCategory W) :
    canonicalDerivedSquareComparison p1 p2 i b hb ((derivedPullback t).obj E) ≫
      (derivedPullback b).map (canonicalDerivedSquareComparison p p1 t a ha E) ≫
      (canonicalDerivedPullbackComposition b a ≪≫
        eqToIso (congrArg (fun q ↦ derivedPullback q) hab)).hom.app
          ((derivedPullback p).obj E) =
    (derivedPullback p2).map
      ((canonicalDerivedPullbackComposition i t ≪≫
        eqToIso (congrArg (fun q ↦ derivedPullback q) h)).hom.app E) ≫
      canonicalDerivedSquareComparison p p2 t' a' ha' E := by
  classical
  subst t'
  subst a'
  let c := @canonicalDerivedPullbackComposition.{v, v + 1}
  have assoc := fun {P Q R S : Scheme.{v}}
      (r : P ⟶ Q) (s : Q ⟶ R) (z : R ⟶ S) ↦
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2.choose_spec.2.2 r s z
  have hbp := congrArg (fun z ↦ z.hom.app E) (assoc b p1 t)
  have hpi := congrArg (fun z ↦ z.hom.app E) (assoc p2 i t)
  have hba := congrArg (fun z ↦ z.hom.app E) (assoc b a p)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app,
    Functor.comp_obj, Category.id_comp] at hbp hpi hba
  change (derivedPullback b).map ((c p1 t).hom.app E) ≫
      (c b (p1 ≫ t)).hom.app E =
    (c b p1).hom.app ((derivedPullback t).obj E) ≫ (c (b ≫ p1) t).hom.app E ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj E) (Category.assoc b p1 t)) at hbp
  change (derivedPullback p2).map ((c i t).hom.app E) ≫
      (c p2 (i ≫ t)).hom.app E =
    (c p2 i).hom.app ((derivedPullback t).obj E) ≫ (c (p2 ≫ i) t).hom.app E ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj E) (Category.assoc p2 i t)) at hpi
  change (derivedPullback b).map ((c a p).hom.app E) ≫
      (c b (a ≫ p)).hom.app E =
    (c b a).hom.app ((derivedPullback p).obj E) ≫ (c (b ≫ a) p).hom.app E ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj E) (Category.assoc b a p)) at hba
  have mid : (c b (p1 ≫ t)).hom.app E ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback (b ≫ s)).obj E) ha.symm) =
      (derivedPullback b).map
        (eqToHom (congrArg (fun s ↦ (derivedPullback s).obj E) ha.symm)) ≫
        (c b (a ≫ p)).hom.app E := by
    simpa only [Iso.app_hom, eqToHom_map] using
      eqToHom_iso_hom_naturality (fun s : B ⟶ W ↦ (c b s).app E) ha.symm
  have midhb : (c (p2 ≫ i) t).hom.app E ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback (s ≫ t)).obj E) hb.symm) =
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj
        ((derivedPullback t).obj E)) hb.symm) ≫ (c (b ≫ p1) t).hom.app E := by
    simpa only [Iso.app_hom, eqToHom_map] using
      eqToHom_iso_hom_naturality (fun s : C ⟶ T ↦ (c s t).app E) hb.symm
  have compare :
      (c p2 i).hom.app ((derivedPullback t).obj E) ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj
          ((derivedPullback t).obj E)) hb.symm) ≫
        (c b p1).inv.app ((derivedPullback t).obj E) ≫
        (derivedPullback b).map ((c p1 t).hom.app E ≫
          eqToHom (congrArg (fun s ↦ (derivedPullback s).obj E) ha.symm) ≫
          (c a p).inv.app E) =
      (derivedPullback p2).map ((c i t).hom.app E) ≫
        (c p2 (i ≫ t)).hom.app E ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj E) ha'.symm) ≫
        (c (b ≫ a) p).inv.app E ≫ (c b a).inv.app ((derivedPullback p).obj E) := by
    apply (cancel_mono ((derivedPullback b).map ((c a p).hom.app E) ≫
      (c b (a ≫ p)).hom.app E)).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (derivedPullback b)
      ((c a p).inv.app E) ((c a p).hom.app E), Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.id_comp, ← mid, reassoc_of% hbp]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← reassoc_of% midhb]
    rw [hba]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [reassoc_of% hpi]
    simp only [eqToHom_trans]
  have final := (Iso.eq_comp_inv ((c b a).app
    ((derivedPullback p).obj E))).mp
      (by simpa only [Iso.app_inv, Functor.comp_obj, ← Category.assoc] using compare)
  simpa only [canonicalDerivedSquareComparison, c, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id, Category.assoc,
    Iso.app_hom, Functor.comp_obj, Category.id_comp] using final


end
end AlgebraicGeometry
