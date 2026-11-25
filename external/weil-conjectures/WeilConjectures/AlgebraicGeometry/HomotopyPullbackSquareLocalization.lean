/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Localization of the canonical homotopy pullback square

Source: Stacks Project, Tags 0D5S and 0DVC.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section

/-- The canonical pullback square, descended termwise to homotopy categories.
Its composition comparisons are conjugate to the recorded pushforward comparisons.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-homotopy-pullback-square-localization). -/
def moduleHomotopyPullbackSquare
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive] :
    (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback f').mapHomotopyCategory (.up ℤ) ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ) := by
  let adj := fun {A B : Scheme.{u}} (k : A ⟶ B) ↦
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  let c := fun {A B C : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ C) ↦
    (conjugateIsoEquiv (adj (k ≫ l)) ((adj l).comp (adj k))).symm
      (Scheme.Modules.pushforwardComp k l).symm
  let t := c f' g ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback h.symm) ≪≫ (c p f).symm
  exact (Functor.mapHomotopyCategoryCompIso t (.up ℤ)).hom ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (Scheme.Modules.tensorPullback f ⋙ Scheme.Modules.tensorPullback p)) (.up ℤ)).inv

private noncomputable def pinnedCounit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(Scheme.Modules.tensorPullback f).Additive] :
    DerivedCategory.Qh ⋙ derivedPullback.{u, w} f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) f

private noncomputable def pinnedComp
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback.{u, w} g ⋙ derivedPullback.{u, w} f ≅ derivedPullback.{u, w} (f ≫ g) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) f g

private noncomputable def tensorComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.tensorPullback (f ≫ g) :=
  (conjugateIsoEquiv
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
    (Scheme.Modules.pushforwardComp f g).symm

private theorem composition_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (f ≫ g)).Additive]
    (M : HomotopyCategory Z.Modules (.up ℤ)) :
    (pinnedComp f g).hom.app (DerivedCategory.Qh.obj M) ≫
        (pinnedCounit (f ≫ g)).app M =
      (derivedPullback f).map ((pinnedCounit g).app M) ≫
        (pinnedCounit f).app
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (tensorComp f g) (.up ℤ)).hom.app M) := by
  have hL := @Classical.choose _ _ (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  change (pinnedComp f g).hom = _ at hc
  have hder := hL (f ≫ g)
  have hf := congrArg
    (fun t ↦ t.app (DerivedCategory.Qh.obj M) ≫ (pinnedCounit (f ≫ g)).app M) hc
  simpa only [pinnedCounit, tensorComp, Functor.leftDerived_fac_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.id_comp, Category.comp_id] using hf

private theorem homotopy_comp_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (M : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app M =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app M := by
  rfl

private theorem homotopy_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (M : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).inv.app M =
      (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app M := by
  rfl

private theorem square_pasting
    {C : Type*} [Category C] {A B D E F G H : C}
    (u : A ⟶ B) (v : B ⟶ D) (w : E ≅ D)
    (εB : B ⟶ F) (εD : D ⟶ G) (b : E ⟶ H)
    {I : C} (a : A ⟶ I) (l : I ≅ F) (j : H ≅ G) (t : F ⟶ G)
    (hu : u ≫ εB = a ≫ l.hom) (hw : w.hom ≫ εD = b ≫ j.hom)
    (hv : v ≫ εD = εB ≫ t) :
    u ≫ v ≫ w.inv ≫ b = a ≫ l.hom ≫ t ≫ j.inv := by
  have hi : w.inv ≫ b = εD ≫ j.inv := by
    apply (cancel_mono j.hom).1
    simp only [Category.assoc]
    rw [← hw, w.inv_hom_id_assoc, j.inv_hom_id, Category.comp_id]
  rw [hi, ← Category.assoc v εD, hv]
  simp only [Category.assoc]
  rw [← Category.assoc u εB, hu]
  simp only [Category.assoc]

private theorem square_pasting_map
    {C : Type*} [Category C]
    {A B V U W J I T Z Z' K K' : C}
    (u : A ⟶ B) (v : B ⟶ V) (w : I ≅ V)
    (εB : B ⟶ U) (εV : V ⟶ W)
    (b : I ⟶ T) (εT : T ⟶ Z) (x : T ⟶ K) (εK : K ⟶ K')
    (d₁ : A ⟶ J) (d₂ : J ⟶ Z') (l : Z' ≅ U) (j : Z ≅ W)
    (t : U ⟶ W) (s : Z' ⟶ Z) (y : Z ⟶ K') (e : I ⟶ K) (z : Z' ⟶ K')
    (hu : u ≫ εB = d₁ ≫ d₂ ≫ l.hom)
    (hw : w.hom ≫ εV = b ≫ εT ≫ j.hom)
    (hv : v ≫ εV = εB ≫ t)
    (hs : l.hom ≫ t ≫ j.inv = s)
    (hn : x ≫ εK = εT ≫ y) (he : e = b ≫ x) (hz : z = s ≫ y) :
    u ≫ v ≫ w.inv ≫ e ≫ εK = d₁ ≫ d₂ ≫ z := by
  have hu' : u ≫ εB = (d₁ ≫ d₂) ≫ l.hom := by
    simpa only [Category.assoc] using hu
  have hp := square_pasting u v w εB εV (b ≫ εT) (d₁ ≫ d₂) l j t
    hu' (by simpa only [Category.assoc] using hw) hv
  rw [he, hz]
  simp only [Category.assoc]
  rw [hn]
  calc
    u ≫ v ≫ w.inv ≫ b ≫ εT ≫ y = d₁ ≫ d₂ ≫ l.hom ≫ t ≫ j.inv ≫ y := by
      simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ y) hp
    _ = d₁ ≫ d₂ ≫ s ≫ y := by
      simpa only [Category.assoc] using congrArg (fun q ↦ d₁ ≫ d₂ ≫ q ≫ y) hs

private theorem homotopy_square
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive D'] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {F' : C ⥤ D'} {G' : D' ⥤ E}
    {H I : C ⥤ E} [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H) (t : H ≅ I) (d : F' ⋙ G' ≅ I)
    (M : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (e ≪≫ t ≪≫ d.symm) (.up ℤ)).hom.app M ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ G')) (.up ℤ)).inv.app M =
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app M ≫
        (NatTrans.mapHomotopyCategory t.hom (.up ℤ)).app M ≫
        (Functor.mapHomotopyCategoryCompIso d (.up ℤ)).inv.app M := by
  simp only [homotopy_comp_hom, homotopy_comp_inv, Iso.trans_hom, Iso.symm_hom,
    NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app, Iso.refl_inv,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app, Category.comp_id]

private theorem homotopy_square_transformation
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive D'] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {F' : C ⥤ D'} {G' : D' ⥤ E}
    {H I : C ⥤ E} [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H) (t : H ≅ I) (d : F' ⋙ G' ≅ I)
    :
    (Functor.mapHomotopyCategoryCompIso (e ≪≫ t ≪≫ d.symm) (.up ℤ)).hom ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ G')) (.up ℤ)).inv =
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory t.hom (.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso d (.up ℤ)).inv := by
  ext M
  exact homotopy_square e t d M

private theorem square_comparisons_transformation
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    [(Scheme.Modules.tensorPullback (f' ≫ g)).Additive]
    [(Scheme.Modules.tensorPullback (p ≫ f)).Additive]
    :
    moduleHomotopyPullbackSquare f f' g p h =
      (Functor.mapHomotopyCategoryCompIso (tensorComp f' g) (.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory
          (eqToHom (congrArg Scheme.Modules.tensorPullback h.symm)) (.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (tensorComp p f) (.up ℤ)).inv := by
  simpa only [moduleHomotopyPullbackSquare, tensorComp, eqToIso.hom] using
    homotopy_square_transformation (tensorComp f' g)
      (eqToIso (congrArg Scheme.Modules.tensorPullback h.symm)) (tensorComp p f)

private theorem square_comparisons
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    [(Scheme.Modules.tensorPullback (f' ≫ g)).Additive]
    [(Scheme.Modules.tensorPullback (p ≫ f)).Additive]
    (M : HomotopyCategory S.Modules (.up ℤ)) :
    (moduleHomotopyPullbackSquare f f' g p h).app M =
      (Functor.mapHomotopyCategoryCompIso (tensorComp f' g) (.up ℤ)).hom.app M ≫
        (NatTrans.mapHomotopyCategory
          (eqToHom (congrArg Scheme.Modules.tensorPullback h.symm)) (.up ℤ)).app M ≫
        (Functor.mapHomotopyCategoryCompIso (tensorComp p f) (.up ℤ)).inv.app M := by
  simpa only [NatTrans.comp_app] using
    NatTrans.congr_app (square_comparisons_transformation f f' g p h) M

private theorem square_localization_aux
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {X Y : Scheme.{u}} (k : X ⟶ Y), (Scheme.Modules.tensorPullback k).Additive]
    (ε : ∀ {X Y : Scheme.{u}} (k : X ⟶ Y),
      DerivedCategory.Qh ⋙ derivedPullback k ⟶
        (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (c : ∀ {X Y Z : Scheme.{u}} (k : X ⟶ Y) (l : Y ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l))
    (fac : ∀ {X Y Z : Scheme.{u}} (k : X ⟶ Y) (l : Y ⟶ Z)
      (M : HomotopyCategory Z.Modules (.up ℤ)),
      (c k l).hom.app (DerivedCategory.Qh.obj M) ≫ (ε (k ≫ l)).app M =
        (derivedPullback k).map ((ε l).app M) ≫
          (ε k).app (((Scheme.Modules.tensorPullback l).mapHomotopyCategory (.up ℤ)).obj M) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (tensorComp k l) (.up ℤ)).hom.app M))
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    (M : HomotopyCategory S.Modules (.up ℤ))
    (K : HomotopyCategory X.Modules (.up ℤ))
    (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj M ⟶ K) :
    (c f' g).hom.app (DerivedCategory.Qh.obj M) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj (DerivedCategory.Qh.obj M)) h.symm) ≫
      (c p f).inv.app (DerivedCategory.Qh.obj M) ≫
      (derivedPullback p).map ((ε f).app M ≫ DerivedCategory.Qh.map a) ≫
      (ε p).app K =
    (derivedPullback f').map ((ε g).app M) ≫
      (ε f').app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj M) ≫
      DerivedCategory.Qh.map ((moduleHomotopyPullbackSquare f f' g p h).app M ≫
        ((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map a) := by
  have ht :
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj (DerivedCategory.Qh.obj M)) h.symm) ≫
        (ε (p ≫ f)).app M =
      (ε (f' ≫ g)).app M ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (eqToHom (congrArg Scheme.Modules.tensorPullback h.symm)) (.up ℤ)).app M) := by
    generalize hk : f' ≫ g = k at *
    generalize hl : p ≫ f = l at *
    cases h
    simp only [eqToHom_refl, Category.id_comp, NatTrans.mapHomotopyCategory_id,
      NatTrans.id_app]
    rw [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  exact square_pasting_map (C := schemeDerivedCategory.{u, w} X')
    ((c f' g).hom.app (DerivedCategory.Qh.obj M))
    (eqToHom (congrArg (fun k ↦ (derivedPullback k).obj (DerivedCategory.Qh.obj M)) h.symm))
    ((c p f).app (DerivedCategory.Qh.obj M))
    ((ε (f' ≫ g)).app M) ((ε (p ≫ f)).app M)
    ((derivedPullback p).map ((ε f).app M))
    ((ε p).app
      (((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj M))
    ((derivedPullback p).map (DerivedCategory.Qh.map a)) ((ε p).app K)
    ((derivedPullback f').map ((ε g).app M))
    ((ε f').app
      (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj M))
    ((DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))).mapIso
      ((Functor.mapHomotopyCategoryCompIso (tensorComp f' g) (.up ℤ)).app M))
    ((DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))).mapIso
      ((Functor.mapHomotopyCategoryCompIso (tensorComp p f) (.up ℤ)).app M))
    (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
      (eqToHom (congrArg Scheme.Modules.tensorPullback h.symm)) (.up ℤ)).app M))
    (DerivedCategory.Qh.map ((moduleHomotopyPullbackSquare f f' g p h).app M))
    (DerivedCategory.Qh.map
      (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map a))
    ((derivedPullback p).map ((ε f).app M ≫ DerivedCategory.Qh.map a))
    (DerivedCategory.Qh.map ((moduleHomotopyPullbackSquare f f' g p h).app M ≫
      ((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map a))
    (by simpa only [Category.assoc, CategoryTheory.Functor.mapIso_hom, Iso.app_hom] using
      fac f' g M)
    (by simpa only [Category.assoc, CategoryTheory.Functor.mapIso_hom, Iso.app_hom] using
      fac p f M)
    ht
    (by
      simpa only [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
        Iso.app_hom, Iso.app_inv, CategoryTheory.Functor.map_comp] using
        ((DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))).congr_map
            (square_comparisons f f' g p h M)).symm)
    ((ε p).naturality a)
    ((derivedPullback p).map_comp _ _)
    (DerivedCategory.Qh.map_comp _ _)


/-- Localization carries the canonical pullback square to the pinned derived square,
including the left-derived counits and any map out of the ordinary pullback.
There are no pushforward units, derived adjunctions or acyclicity hypotheses here.
Source: Stacks Project, Tag 0D5S, compatibility of composite derived pullbacks;
Tag 0DVC, compatibility with localization.
(blueprint: lem-pc-homotopy-pullback-square-localization).

Proof: The defining left-derived lift factorization for c(f',g) identifies its
composite with the counit for f' g with Lf'(delta_g) followed by delta_f' and
localization of the ordinary composition comparison. Apply the same factorization
to c(p,f), and cancel its invertible component to express its inverse followed by
Lp(delta_f) and delta_p. Transport the composite counit across p f = f' g;
equality elimination identifies both transports. Compose the two factorizations:
the ordinary comparisons combine into moduleHomotopyPullbackSquare. Finally use
naturality of delta_p at a and functoriality of Qh to move the localized a to the
right. This is an identity of natural transformations, so it applies to arbitrary
M, K and a, including zero complexes and identity squares. -/
theorem homotopyPullbackSquare_localization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (M : HomotopyCategory S.Modules (.up ℤ))
    (K : HomotopyCategory X.Modules (.up ℤ))
    (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj M ⟶ K) :
    let ε := @Classical.choose _ _ (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    (c f' g).hom.app (DerivedCategory.Qh.obj M) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj (DerivedCategory.Qh.obj M)) h.symm) ≫
      (c p f).inv.app (DerivedCategory.Qh.obj M) ≫
      (derivedPullback p).map ((ε f).app M ≫ DerivedCategory.Qh.map a) ≫
      (ε p).app K =
    (derivedPullback f').map ((ε g).app M) ≫
      (ε f').app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj M) ≫
      DerivedCategory.Qh.map ((moduleHomotopyPullbackSquare f f' g p h).app M ≫
        ((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map a) := by
  have : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      (Scheme.Modules.tensorPullback k).Additive :=
    @Classical.choose _ _ exists_derivedPullbackComposition.{u, w}
  dsimp only
  exact square_localization_aux
    (@Classical.choose _ _ (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))
    (@Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))))
    (fun k l N ↦ composition_counit k l N) f f' g p h M K a

end
end AlgebraicGeometry
