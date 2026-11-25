/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Horizontal composition of ordinary derived base-change maps

Source: Stacks Project, Tag 0ATM, and the counit formula of Tag 08HY.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- Ordinary base-change maps paste horizontally before any invertibility assumption.
Source: Stacks Project, Tag 0ATM (composition of base change), Tag 08HY (counit formula),
and Tag 0D5S (associativity of derived pullback).
(blueprint: lem-pc-derived-base-change-horizontal-pasting)

Proof: Transpose both sides under the pinned adjunction for r. Naturality of the
composition comparison c(r,h) moves the first base-change map through it. The
commutativity equality and naturality of c(t,q) then move it through the comparison
between pullbacks along r followed by h and t followed by q. The counit formula for
the second square gives pullback along t of the counit for q. The first base-change
map is a transpose under the pinned adjunction for q, so its pullback followed by
this counit is exactly its defining transpose. Substitute that transpose. The
associativity identity for c, for r,h,g and for t,p,f, and the two square equalities
identify the resulting composite with the transpose of the outer square, preceded
by c(h,g) and followed by c(t,p) inverse. Equality transports agree by proof
irrelevance. Injectivity of the Hom equivalence for r proves the formula. This
uses only adjunction and functor identities, including for empty schemes, zero
objects, or identity arrows; no cartesian or invertibility assumption is needed. -/
theorem schemeDerivedBaseChange_horizontal_pasting
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y P S I T : Scheme.{u}}
    (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S)
    (p : P ⟶ X) (q : P ⟶ S) (t : I ⟶ P) (r : I ⟶ T)
    (hs : p ≫ f = q ≫ g) (hi : t ≫ q = r ≫ h) :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    ∀ E : schemeDerivedCategory X,
      (derivedPullback h).map (schemeDerivedBaseChangeMap f q g p hs E) ≫
          schemeDerivedBaseChangeMap q r h t hi ((derivedPullback p).obj E) =
        (c h g).hom.app ((schemeDerivedDirectImage f).obj E) ≫
          schemeDerivedBaseChangeMap f r (h ≫ g) (t ≫ p)
            (by rw [Category.assoc, hs, ← Category.assoc t q g, hi, Category.assoc]) E ≫
          (schemeDerivedDirectImage r).map ((c t p).inv.app E)  := by
  classical
  intro c E
  let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
    Classical.choose (exists_schemeDerivedAdjunction s
      (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) s))
  let ho : (t ≫ p) ≫ f = r ≫ (h ≫ g) := by
    rw [Category.assoc, hs, ← Category.assoc t q g, hi, Category.assoc]
  let M := (schemeDerivedDirectImage f).obj E
  let bs : (derivedPullback q).obj ((derivedPullback g).obj M) ⟶
      (derivedPullback p).obj E :=
    (c q g).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) hs.symm) ≫
      (c p f).inv.app M ≫ (derivedPullback p).map ((a f).counit.app E)
  let bo : (derivedPullback r).obj ((derivedPullback (h ≫ g)).obj M) ⟶
      (derivedPullback (t ≫ p)).obj E :=
    (c r (h ≫ g)).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) ho.symm) ≫
      (c (t ≫ p) f).inv.app M ≫
      (derivedPullback (t ≫ p)).map ((a f).counit.app E)
  let β := (a q).homEquiv _ _ bs
  let bi : (derivedPullback r).obj ((derivedPullback h).obj
      ((schemeDerivedDirectImage q).obj ((derivedPullback p).obj E))) ⟶
      (derivedPullback t).obj ((derivedPullback p).obj E) :=
    (c r h).hom.app ((schemeDerivedDirectImage q).obj ((derivedPullback p).obj E)) ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj
        ((schemeDerivedDirectImage q).obj ((derivedPullback p).obj E))) hi.symm) ≫
      (c t q).inv.app ((schemeDerivedDirectImage q).obj ((derivedPullback p).obj E)) ≫
      (derivedPullback t).map ((a q).counit.app ((derivedPullback p).obj E))
  change (derivedPullback h).map β ≫ (a r).homEquiv _ _ bi =
    (c h g).hom.app M ≫ (a r).homEquiv _ _ bo ≫
      (schemeDerivedDirectImage r).map ((c t p).inv.app E)
  rw [← (a r).homEquiv_naturality_right,
    ← (a r).homEquiv_naturality_left, ← (a r).homEquiv_naturality_left]
  apply congrArg ((a r).homEquiv _ _)
  have hβ : (derivedPullback q).map β ≫
      (a q).counit.app ((derivedPullback p).obj E) = bs := by
    exact ((a q).homEquiv _ _).symm_apply_apply bs
  have transport {A : Scheme.{u}} (s s' : I ⟶ A) (e : s = s')
      {N N' : schemeDerivedCategory A} (v : N ⟶ N') :
      (derivedPullback s).map v ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj N') e) =
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj N) e) ≫
        (derivedPullback s').map v := by
    cases e
    simp
  have left : (derivedPullback r).map ((derivedPullback h).map β) ≫ bi =
      (c r h).hom.app ((derivedPullback g).obj M) ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj
          ((derivedPullback g).obj M)) hi.symm) ≫
        (c t q).inv.app ((derivedPullback g).obj M) ≫
        (derivedPullback t).map bs := by
    dsimp only [bi]
    rw [← Functor.comp_map, (c r h).hom.naturality_assoc,
      reassoc_of% (transport _ _ hi.symm β), (c t q).inv.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp, hβ]
  rw [left]
  have assoc := fun {A B C D : Scheme.{u}}
      (r : A ⟶ B) (s : B ⟶ C) (v : C ⟶ D) ↦
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2.choose_spec.2.2 r s v
  have htq := congrArg (fun z ↦ z.hom.app M) (assoc t q g)
  have hrh := congrArg (fun z ↦ z.hom.app M) (assoc r h g)
  have htp := congrArg (fun z ↦ z.hom.app M) (assoc t p f)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app,
    Functor.comp_obj, Category.id_comp] at htq hrh htp
  change (derivedPullback t).map ((c q g).hom.app M) ≫
      (c t (q ≫ g)).hom.app M =
    (c t q).hom.app ((derivedPullback g).obj M) ≫ (c (t ≫ q) g).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) (Category.assoc t q g)) at htq
  change (derivedPullback r).map ((c h g).hom.app M) ≫
      (c r (h ≫ g)).hom.app M =
    (c r h).hom.app ((derivedPullback g).obj M) ≫ (c (r ≫ h) g).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) (Category.assoc r h g)) at hrh
  change (derivedPullback t).map ((c p f).hom.app M) ≫
      (c t (p ≫ f)).hom.app M =
    (c t p).hom.app ((derivedPullback f).obj M) ≫ (c (t ≫ p) f).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) (Category.assoc t p f)) at htp
  have mid : (c t (q ≫ g)).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback (t ≫ s)).obj M) hs.symm) =
      (derivedPullback t).map
        (eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) hs.symm)) ≫
        (c t (p ≫ f)).hom.app M := by
    simpa only [Iso.app_hom, eqToHom_map] using
      eqToHom_iso_hom_naturality (fun s : P ⟶ Y ↦ (c t s).app M) hs.symm
  have midhi : (c (r ≫ h) g).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback (s ≫ g)).obj M) hi.symm) =
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj
        ((derivedPullback g).obj M)) hi.symm) ≫ (c (t ≫ q) g).hom.app M := by
    simpa only [Iso.app_hom, eqToHom_map] using
      eqToHom_iso_hom_naturality (fun s : I ⟶ S ↦ (c s g).app M) hi.symm
  have compare :
      (c r h).hom.app ((derivedPullback g).obj M) ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj
          ((derivedPullback g).obj M)) hi.symm) ≫
        (c t q).inv.app ((derivedPullback g).obj M) ≫
        (derivedPullback t).map ((c q g).hom.app M ≫
          eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) hs.symm) ≫
          (c p f).inv.app M) =
      (derivedPullback r).map ((c h g).hom.app M) ≫
        (c r (h ≫ g)).hom.app M ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) ho.symm) ≫
        (c (t ≫ p) f).inv.app M ≫ (c t p).inv.app ((derivedPullback f).obj M) := by
    apply (cancel_mono ((derivedPullback t).map ((c p f).hom.app M) ≫
      (c t (p ≫ f)).hom.app M)).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (derivedPullback t)
      ((c p f).inv.app M) ((c p f).hom.app M), Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.id_comp, ← mid, reassoc_of% htq]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← reassoc_of% midhi]
    rw [htp]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [reassoc_of% hrh]
    simp only [eqToHom_trans]
  dsimp only [bs, bo]
  simp only [Category.assoc, Functor.map_comp]
  have hn : (derivedPullback (t ≫ p)).map ((a f).counit.app E) ≫
      (c t p).inv.app E = (c t p).inv.app ((derivedPullback f).obj M) ≫
        (derivedPullback t).map ((derivedPullback p).map ((a f).counit.app E)) :=
    (c t p).inv.naturality ((a f).counit.app E)
  rw [hn]
  simpa only [M, Functor.comp_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ z ≫ (derivedPullback t).map
      ((derivedPullback p).map ((a f).counit.app E))) compare

end AlgebraicGeometry
