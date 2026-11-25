/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Pasting coefficient-restriction squares

Source: Stacks Project, Tag 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

section
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
variable
  (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g))
  (hc : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
    Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
      Functor.associator (derivedPullback g) (derivedPullback f)
          (derivedPullback h) ≪≫
        Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
          eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
            (Category.assoc h f g)))
include hc
private theorem comp_assoc {W X Y Z : Scheme.{u}}
    (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (K : schemeDerivedCategory Z) :
    (derivedPullback h).map ((c f g).hom.app K) ≫ (c h (f ≫ g)).hom.app K =
      (c h f).hom.app ((derivedPullback g).obj K) ≫ (c (h ≫ f) g).hom.app K ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) (Category.assoc h f g)) := by
  have hcomp := congrArg (fun t ↦ t.hom.app K) (hc h f g)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app, Category.id_comp] using hcomp

private theorem pasted_comparison
    {X X' W A P B : Scheme.{u}}
    (g : X' ⟶ X) (w : W ⟶ X) (a : A ⟶ W)
    (p : P ⟶ X') (q : P ⟶ W) (r : B ⟶ P) (t : B ⟶ A)
    (h : q ≫ w = p ≫ g) (h2 : t ≫ a = r ≫ q)
    (hrect : t ≫ (a ≫ w) = (r ≫ p) ≫ g)
    (K : schemeDerivedCategory X) :
    (c t a).hom.app ((derivedPullback w).obj K) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj
        ((derivedPullback w).obj K)) h2) ≫
      (c r q).inv.app ((derivedPullback w).obj K) ≫
      (derivedPullback r).map ((c q w).hom.app K ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) h) ≫
        (c p g).inv.app K) ≫
      (c r p).hom.app ((derivedPullback g).obj K) =
    (derivedPullback t).map ((c a w).hom.app K) ≫
      (c t (a ≫ w)).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hrect) ≫
      (c (r ≫ p) g).inv.app K := by
  have htaw := comp_assoc c hc t a w K
  have hrqw := comp_assoc c hc r q w K
  have hrpg := comp_assoc c hc r p g K
  have htarget : (c r p).hom.app ((derivedPullback g).obj K) ≫
      (c (r ≫ p) g).hom.app K =
      (derivedPullback r).map ((c p g).hom.app K) ≫
      (c r (p ≫ g)).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (Category.assoc r p g).symm) := by
    apply (cancel_mono (eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (Category.assoc r p g)))).mp
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      using hrpg.symm
  apply (cancel_mono ((c (r ≫ p) g).hom.app K)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [htarget]
  have hcancel : (derivedPullback r).map ((c p g).inv.app K) ≫
      (derivedPullback r).map ((c p g).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [reassoc_of% hcancel]
  have hn := eqToHom_naturality (fun k : P ⟶ X ↦ (c r k).hom.app K) h
  rw [eqToHom_map, ← reassoc_of% hn]
  rw [reassoc_of% hrqw]
  simp only [Iso.inv_hom_id_app_assoc]
  have hn2 := eqToHom_naturality (fun k : B ⟶ W ↦ (c k w).hom.app K) h2
  rw [← reassoc_of% hn2]
  rw [reassoc_of% htaw]
  simp only [eqToHom_trans]

end

/-- Restricting a coefficient map across two commutative squares agrees with
restriction across their pasted rectangle, in the composition coordinates.
Source: Stacks Project, Tag 0D5S, associativity and naturality of derived pullback.
(blueprint: lem-pc-coefficient-square-pasting).

Proof: Expand the two square maps. Use functoriality to distribute the outer
pullback over the first square's four factors. Naturality of the comparison
c(r,p) moves the pulled-back coefficient morphism to the end. Apply the
associativity law to (t,a,w) and (r,q,w) to merge the source factors and to
(r,p,g) to merge the target factors. The equations h and h2 identify the
resulting composite scheme morphisms with the rectangle. Naturality of
 eqToHom combines their transports into the transport along hrect; proof
irrelevance identifies the proofs of this equality. Cancel the intermediate
comparison and its inverse. The remaining factors are exactly the rectangle
map preceded by the source composition and followed by the inverse target
composition. This uses no pullback universal property or geometric hypothesis,
so also covers empty schemes, zero coefficients and identity arrows. -/
theorem coefficient_square_pasting
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' W A P B : Scheme.{u}}
    (g : X' ⟶ X) (w : W ⟶ X) (a : A ⟶ W)
    (p : P ⟶ X') (q : P ⟶ W) (r : B ⟶ P) (t : B ⟶ A)
    (h : q ≫ w = p ≫ g) (h2 : t ≫ a = r ≫ q)
    (hrect : t ≫ (a ≫ w) = (r ≫ p) ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (phi : (derivedPullback g).obj K ⟶ K') :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let KW := (derivedPullback w).obj K
    let phiW := (c q w).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) h) ≫
      (c p g).inv.app K ≫ (derivedPullback p).map phi
    let phiA := (c t a).hom.app KW ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KW) h2) ≫
      (c r q).inv.app KW ≫ (derivedPullback r).map phiW
    let phiRect := (c t (a ≫ w)).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hrect) ≫
      (c (r ≫ p) g).inv.app K ≫ (derivedPullback (r ≫ p)).map phi
    phiA = (derivedPullback t).map ((c a w).hom.app K) ≫ phiRect ≫
      (c r p).inv.app K' := by
  classical
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let KW := (derivedPullback w).obj K
  let phiW := (c q w).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) h) ≫
    (c p g).inv.app K ≫ (derivedPullback p).map phi
  let phiA := (c t a).hom.app KW ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KW) h2) ≫
    (c r q).inv.app KW ≫ (derivedPullback r).map phiW
  let phiRect := (c t (a ≫ w)).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hrect) ≫
    (c (r ≫ p) g).inv.app K ≫ (derivedPullback (r ≫ p)).map phi
  have hc : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
        Functor.associator (derivedPullback g) (derivedPullback f)
            (derivedPullback h) ≪≫
          Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
              (Category.assoc h f g)) := by
    exact (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))).2).2.2
  have hcomparison := pasted_comparison c hc g w a p q r t h h2 hrect K
  have hn : (derivedPullback r).map ((derivedPullback p).map phi) ≫
      (c r p).hom.app K' =
      (c r p).hom.app ((derivedPullback g).obj K) ≫
        (derivedPullback (r ≫ p)).map phi := (c r p).hom.naturality phi
  have hlast : (derivedPullback r).map ((derivedPullback p).map phi) =
      (c r p).hom.app ((derivedPullback g).obj K) ≫
        (derivedPullback (r ≫ p)).map phi ≫ (c r p).inv.app K' := by
    apply (cancel_mono ((c r p).hom.app K')).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hn
  change phiA = (derivedPullback t).map ((c a w).hom.app K) ≫ phiRect ≫
    (c r p).inv.app K'
  simp only [phiA, phiW, phiRect, Functor.map_comp, Category.assoc]
  rw [hlast]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ f ≫ (derivedPullback (r ≫ p)).map phi ≫
      (c r p).inv.app K') hcomparison


end AlgebraicGeometry
