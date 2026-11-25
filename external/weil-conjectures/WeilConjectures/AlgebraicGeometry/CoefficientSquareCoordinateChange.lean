/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Changing coefficient-square coordinates

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

private theorem coordinate_comparison
    {X X' A Z B PZ : Scheme.{u}}
    (g : X' ⟶ X) (v : A ⟶ X) (z : Z ⟶ X)
    (t : B ⟶ A) (s : B ⟶ X') (qz : PZ ⟶ Z) (pz : PZ ⟶ X')
    (e : A ⟶ Z) (b : B ⟶ PZ)
    (hv : e ≫ z = v) (ht : b ≫ qz = t ≫ e) (hs : b ≫ pz = s)
    (hz : qz ≫ z = pz ≫ g) (hrect : t ≫ v = s ≫ g)
    (K : schemeDerivedCategory X) :
    (derivedPullback t).map ((c e z).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hv)) ≫
      (c t v).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hrect) ≫
      (c s g).inv.app K =
      (c t e).hom.app ((derivedPullback z).obj K) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj
        ((derivedPullback z).obj K)) ht.symm) ≫
      (c b qz).inv.app ((derivedPullback z).obj K) ≫
      (derivedPullback b).map ((c qz z).hom.app K ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hz) ≫
        (c pz g).inv.app K) ≫
      (c b pz).hom.app ((derivedPullback g).obj K) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj
        ((derivedPullback g).obj K)) hs) := by
  have htez := comp_assoc c hc t e z K
  have hbqz := comp_assoc c hc b qz z K
  have hbpg := comp_assoc c hc b pz g K
  have htarget : (c b pz).hom.app ((derivedPullback g).obj K) ≫
      (c (b ≫ pz) g).hom.app K =
      (derivedPullback b).map ((c pz g).hom.app K) ≫
      (c b (pz ≫ g)).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (Category.assoc b pz g).symm) := by
    apply (cancel_mono (eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (Category.assoc b pz g)))).mp
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      using hbpg.symm
  have hcancel : (derivedPullback b).map ((c pz g).inv.app K) ≫
      (derivedPullback b).map ((c pz g).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  apply (cancel_mono ((c s g).hom.app K)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hns := eqToHom_naturality (fun k : B ⟶ X' ↦ (c k g).hom.app K) hs
  rw [← hns, reassoc_of% htarget]
  simp only [reassoc_of% hcancel]
  have hnz := eqToHom_naturality (fun k : PZ ⟶ X ↦ (c b k).hom.app K) hz
  simp only [eqToHom_map]
  rw [← reassoc_of% hnz]
  rw [reassoc_of% hbqz]
  simp only [Iso.inv_hom_id_app_assoc]
  have hnt := eqToHom_naturality (fun k : B ⟶ Z ↦ (c k z).hom.app K) ht.symm
  rw [← reassoc_of% hnt]
  have hnv := eqToHom_naturality (fun k : A ⟶ X ↦ (c t k).hom.app K) hv
  rw [← reassoc_of% hnv, reassoc_of% htez]
  simp only [eqToHom_trans]

end

/-- A change of the two coordinates of a commutative coefficient square is
compatible with the composition comparisons. The coordinate arrows need not
be invertible.
Source: Stacks Project, Tag 0D5S, associativity and naturality of derived pullback.
(blueprint: lem-pc-coefficient-square-coordinate-change).

Proof: Expand both square maps. Apply associativity to (t,e,z) and
(b,qz,z) to move the source comparison through the square equality hz;
use ht and hv to identify the composite morphisms. Apply associativity to
(b,pz,g), then naturality at phi, to move the target comparison past the
coefficient morphism. Equality-transport naturality moves the transports to
the common composite. The rectangle equality and the transported square
equality have the same endpoints, so proof irrelevance identifies them.
The forward and inverse comparisons cancel. Both sides now have the same
source comparison, the same equality transport and the same final pullback
of phi. No cancellation of a coordinate arrow is used, so the assertion holds
for arbitrary arrows, including maps from empty schemes and zero coefficients. -/
theorem coefficient_square_coordinate_change
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' A Z B PZ : Scheme.{u}}
    (g : X' ⟶ X) (v : A ⟶ X) (z : Z ⟶ X)
    (t : B ⟶ A) (s : B ⟶ X') (qz : PZ ⟶ Z) (pz : PZ ⟶ X')
    (e : A ⟶ Z) (b : B ⟶ PZ)
    (hv : e ≫ z = v) (ht : b ≫ qz = t ≫ e) (hs : b ≫ pz = s)
    (hz : qz ≫ z = pz ≫ g) (hrect : t ≫ v = s ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (phi : (derivedPullback g).obj K ⟶ K') :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let phiRect := (c t v).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hrect) ≫
      (c s g).inv.app K ≫ (derivedPullback s).map phi
    let phiZ := (c qz z).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hz) ≫
      (c pz g).inv.app K ≫ (derivedPullback pz).map phi
    (derivedPullback t).map ((c e z).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hv)) ≫ phiRect =
      (c t e).hom.app ((derivedPullback z).obj K) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj
        ((derivedPullback z).obj K)) ht.symm) ≫
      (c b qz).inv.app ((derivedPullback z).obj K) ≫
      (derivedPullback b).map phiZ ≫ (c b pz).hom.app K' ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K') hs) := by
  classical
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let phiRect := (c t v).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hrect) ≫
    (c s g).inv.app K ≫ (derivedPullback s).map phi
  let phiZ := (c qz z).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hz) ≫
    (c pz g).inv.app K ≫ (derivedPullback pz).map phi
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
  have hcomparison := coordinate_comparison c hc g v z t s qz pz e b
    hv ht hs hz hrect K
  have hn : (derivedPullback b).map ((derivedPullback pz).map phi) ≫
      (c b pz).hom.app K' =
      (c b pz).hom.app ((derivedPullback g).obj K) ≫
        (derivedPullback (b ≫ pz)).map phi := (c b pz).hom.naturality phi
  have hns := eqToHom_naturality
    (fun k : B ⟶ X' ↦ (derivedPullback k).map phi) hs
  change
  (derivedPullback t).map ((c e z).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hv)) ≫ phiRect =
    (c t e).hom.app ((derivedPullback z).obj K) ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj
      ((derivedPullback z).obj K)) ht.symm) ≫
    (c b qz).inv.app ((derivedPullback z).obj K) ≫
    (derivedPullback b).map phiZ ≫ (c b pz).hom.app K' ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K') hs)
  simp only [phiRect, phiZ, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hns]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ f ≫ (derivedPullback s).map phi) hcomparison


end AlgebraicGeometry
