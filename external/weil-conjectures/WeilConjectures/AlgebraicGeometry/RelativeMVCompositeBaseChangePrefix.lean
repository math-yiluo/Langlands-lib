/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.CoefficientSquarePasting

/-! # The counit for base change of a composite morphism

Source: Stacks Project, Cohomology, Tags 08HY, 08HZ and 0D5S.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_transpose {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R R' : E ⥤ D} (a : L ⊣ R) (a' : L ⊣ R')
    {M : D} {N : E} (b : M ⟶ R'.obj N) :
    (a.homEquiv _ _).symm (b ≫ (a.rightAdjointUniq a').inv.app N) =
      (a'.homEquiv _ _).symm b := by
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.rightAdjointUniq_inv_app,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_counit]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem composite_transpose
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {B X S : Scheme.{u}} (j : B ⟶ X) (f : X ⟶ S)
    (M : schemeDerivedCategory S) (N : schemeDerivedCategory B)
    (b : M ⟶ (schemeDerivedDirectImage (j ≫ f)).obj N) :
    ((relativeMVAdj f).homEquiv _ _).symm
        (b ≫ (relativeMVImageComp j f).inv.app N) =
      (relativeMVAdj j).homEquiv _ _
        ((relativeMVComp j f).hom.app M ≫
          ((relativeMVAdj (j ≫ f)).homEquiv _ _).symm b) := by
  have h := mate_transpose
    (((relativeMVAdj f).comp (relativeMVAdj j)).ofNatIsoLeft (relativeMVComp j f))
    (relativeMVAdj (j ≫ f)) b
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    Adjunction.comp_homEquiv] at h
  dsimp only [Equiv.symm_trans_apply] at h
  have h' := congrArg (fun t ↦ (relativeMVComp j f).hom.app M ≫ t) h
  simp only [Iso.hom_inv_id_app_assoc] at h'
  apply (relativeMVAdj j).homEquiv _ _ |>.symm.injective
  simpa only [Equiv.symm_apply_apply, relativeMVImageComp, Functor.comp_obj] using h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The pasted comparison contains the fixed derived-composition data.
private theorem comparison_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g) (M : schemeDerivedCategory S) (W : X.Opens) :
    let h : pullback.snd g' W.ι ≫ (W.ι ≫ f) =
        (pullback.fst g' W.ι ≫ f') ≫ g := by
      rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]
    let a := (relativeMVComp (pullback.fst g' W.ι ≫ f') g ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫
      (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).symm).app M
    let b := (derivedPullback (pullback.snd g' W.ι)).mapIso
      ((relativeMVComp W.ι f).symm.app M)
    let d := (relativeMVComp (pullback.snd g' W.ι) W.ι ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k)
        (pullback.condition (f := g') (g := W.ι)).symm) ≪≫
      (relativeMVComp (pullback.fst g' W.ι) g').symm).app ((derivedPullback f).obj M)
    let e := (relativeMVComp (pullback.fst g' W.ι) f').symm.app
      ((derivedPullback g).obj M)
    let z := (derivedPullback (pullback.fst g' W.ι)).mapIso
      ((relativeMVComp f' g ≪≫
        eqToIso (congrArg (fun k ↦ derivedPullback k) hpull.w.symm) ≪≫
        (relativeMVComp g' f).symm).app M)
    a.hom ≫ b.hom ≫ d.hom = e.hom ≫ z.hom := by
  dsimp only
  let h : pullback.snd g' W.ι ≫ (W.ι ≫ f) =
      (pullback.fst g' W.ι ≫ f') ≫ g := by
    rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]
  let a := (relativeMVComp (pullback.fst g' W.ι ≫ f') g ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫
    (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).symm).app M
  let b := (derivedPullback (pullback.snd g' W.ι)).mapIso
    ((relativeMVComp W.ι f).symm.app M)
  let d := (relativeMVComp (pullback.snd g' W.ι) W.ι ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (pullback.condition (f := g') (g := W.ι)).symm) ≪≫
    (relativeMVComp (pullback.fst g' W.ι) g').symm).app ((derivedPullback f).obj M)
  let e := (relativeMVComp (pullback.fst g' W.ι) f').symm.app
    ((derivedPullback g).obj M)
  let z := (derivedPullback (pullback.fst g' W.ι)).mapIso
    ((relativeMVComp f' g ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) hpull.w.symm) ≪≫
      (relativeMVComp g' f).symm).app M)
  change a.hom ≫ b.hom ≫ d.hom = e.hom ≫ z.hom
  have hpast := coefficient_square_pasting g f W.ι f' g'
    (pullback.fst g' W.ι) (pullback.snd g' W.ι) hpull.w
    (pullback.condition (f := g') (g := W.ι)).symm h M
    ((derivedPullback g).obj M) (𝟙 _)
  have hd : d.hom ≫ z.inv = b.inv ≫ a.inv ≫ e.hom := by
    simp only [Functor.comp_obj, (derivedPullback f').map_id,
      (derivedPullback (pullback.fst g' W.ι ≫ f')).map_id,
      Category.comp_id, Category.assoc] at hpast
    simp only [a, b, d, e, z, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
      Functor.comp_obj, Category.assoc]
    unfold relativeMVComp
    exact hpast
  have hh := congrArg (fun t ↦ a.hom ≫ b.hom ≫ t ≫ z.hom) hd
  simpa only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc,
    Category.comp_id, Category.id_comp] using hh



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem square_factor
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (M : schemeDerivedCategory S) (N : schemeDerivedCategory X)
    (a : (derivedPullback f).obj M ⟶ N) (W : X.Opens) :
    (relativeMVComp (pullback.fst g' W.ι) f').inv.app ((derivedPullback g).obj M) ≫
      (derivedPullback (pullback.fst g' W.ι)).map
        ((relativeMVComp f' g).hom.app M ≫
          eqToHom (congrArg (fun k ↦ (derivedPullback k).obj M) hpull.w.symm) ≫
          (relativeMVComp g' f).inv.app M ≫ (derivedPullback g').map a) =
    (relativeMVComp (pullback.fst g' W.ι ≫ f') g).hom.app M ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj M)
        (show pullback.snd g' W.ι ≫ (W.ι ≫ f) =
            (pullback.fst g' W.ι ≫ f') ≫ g by
          rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]).symm) ≫
      (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).inv.app M ≫
      (derivedPullback (pullback.snd g' W.ι)).map
        ((relativeMVComp W.ι f).inv.app M ≫ (derivedPullback W.ι).map a) ≫
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app N ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app N := by
  let d := relativeMVComp (pullback.snd g' W.ι) W.ι ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (pullback.condition (f := g') (g := W.ι)).symm) ≪≫
    (relativeMVComp (pullback.fst g' W.ι) g').symm
  have hn := d.hom.naturality a
  simp only [d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Functor.comp_obj, Functor.comp_map] at hn
  have hpast := comparison_pasting f f' g g' hpull M W
  simp only [Functor.mapIso_hom, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.comp_obj,
    Functor.map_comp, Category.assoc] at hpast hn ⊢
  rw [hn]
  simpa only [Category.assoc] using
    (congrArg (fun t ↦ t ≫ (derivedPullback (pullback.fst g' W.ι)).map
      ((derivedPullback g').map a)) hpast).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The right-adjoint composition mate preserves the composite counit. -/
private theorem imageComp_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {B X S : Scheme.{u}} (l : B ⟶ X) (f : X ⟶ S)
    (E : schemeDerivedCategory B) :
    (derivedPullback (l ≫ f)).map ((relativeMVImageComp l f).hom.app E) ≫
        (relativeMVAdj (l ≫ f)).counit.app E =
      (relativeMVComp l f).inv.app
          ((schemeDerivedDirectImage f).obj ((schemeDerivedDirectImage l).obj E)) ≫
        (derivedPullback l).map
          ((relativeMVAdj f).counit.app ((schemeDerivedDirectImage l).obj E)) ≫
        (relativeMVAdj l).counit.app E := by
  simpa only [relativeMVImageComp, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_counit_app,
    Functor.comp_obj,
    Category.assoc] using
    ((((relativeMVAdj f).comp (relativeMVAdj l)).ofNatIsoLeft
      (relativeMVComp l f)).rightAdjointUniq_hom_app_counit
        (relativeMVAdj (l ≫ f)) E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChange_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (K : schemeDerivedCategory X) :
    ((relativeMVAdj f').homEquiv _ _).symm
        (schemeDerivedBaseChangeMap f f' g g' h K) =
      (relativeMVComp f' g).hom.app ((schemeDerivedDirectImage f).obj K) ≫
        eqToHom (congrArg (fun k ↦
          (derivedPullback k).obj ((schemeDerivedDirectImage f).obj K)) h.symm) ≫
        (relativeMVComp g' f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
        (derivedPullback g').map ((relativeMVAdj f).counit.app K) := by
  exact (relativeMVAdj f').homEquiv _ _ |>.symm_apply_apply _


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem imageComp_inv_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {B X S : Scheme.{u}} (j : B ⟶ X) (f : X ⟶ S)
    (E : schemeDerivedCategory B) :
    (relativeMVAdj (j ≫ f)).counit.app E =
      (relativeMVComp j f).inv.app ((schemeDerivedDirectImage (j ≫ f)).obj E) ≫
        (derivedPullback j).map
          ((derivedPullback f).map ((relativeMVImageComp j f).inv.app E) ≫
            (relativeMVAdj f).counit.app ((schemeDerivedDirectImage j).obj E)) ≫
        (relativeMVAdj j).counit.app E := by
  have h := imageComp_counit j f E
  have hi := congrArg (fun t ↦ (derivedPullback (j ≫ f)).map
    ((relativeMVImageComp j f).inv.app E) ≫ t) h
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app] at hi
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hi
  have hn := (relativeMVComp j f).inv.naturality ((relativeMVImageComp j f).inv.app E)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [reassoc_of% hn] at hi
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Transposing the pinned derived adjunctions requires a larger elaboration budget.
private theorem local_transpose
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (U : X.Opens) :
    let C := (schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)
    let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj ((derivedPullback U.ι).obj K)
    let θ := (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' U.ι) g').inv.app K
    ((relativeMVAdj f').homEquiv _ _).symm
        ((relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
            (𝟙 _) U).hom ≫
          (relativeMVImageComp (pullback.fst g' U.ι) f').inv.app
            ((derivedPullback (pullback.fst g' U.ι)).obj
              ((derivedPullback g').obj K))) =
      (relativeMVComp f' g).hom.app A ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A) hpull.w.symm) ≫
        (relativeMVComp g' f).inv.app A ≫
        (derivedPullback g').map
          ((derivedPullback f).map ((relativeMVImageComp U.ι f).inv.app
              ((derivedPullback U.ι).obj K)) ≫ (relativeMVAdj f).counit.app C) ≫
        schemeDerivedBaseChangeMap U.ι (pullback.fst g' U.ι) g'
          (pullback.snd g' U.ι) (pullback.condition (f := g') (g := U.ι)).symm
          ((derivedPullback U.ι).obj K) ≫
        (schemeDerivedDirectImage (pullback.fst g' U.ι)).map θ := by
  dsimp only
  rw [composite_transpose]
  apply ((relativeMVAdj (pullback.fst g' U.ι)).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  unfold relativeMVLocalArrow
  simp only [Arrow.mk_hom, Arrow.mk_left]
  rw [(derivedPullback (pullback.fst g' U.ι)).map_id]
  erw [Category.comp_id]
  rw [Adjunction.homEquiv_naturality_right_symm, baseChange_counit,
    imageComp_inv_counit]
  simp only [← Category.assoc]
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]
  dsimp only [Functor.id_obj]
  rw [baseChange_counit]
  let E := (derivedPullback U.ι).obj K
  let C := (schemeDerivedDirectImage U.ι).obj E
  let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj E
  let a := (derivedPullback f).map ((relativeMVImageComp U.ι f).inv.app E) ≫
    (relativeMVAdj f).counit.app C
  let d := relativeMVComp (pullback.snd g' U.ι) U.ι ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (pullback.condition (f := g') (g := U.ι)).symm) ≪≫
    (relativeMVComp (pullback.fst g' U.ι) g').symm
  have hp := square_factor f f' g g' hpull A C a U
  let r := (relativeMVComp (pullback.fst g' U.ι ≫ f') g).hom.app A ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A)
      (show pullback.snd g' U.ι ≫ (U.ι ≫ f) =
          (pullback.fst g' U.ι ≫ f') ≫ g by
        rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]).symm) ≫
    (relativeMVComp (pullback.snd g' U.ι) (U.ι ≫ f)).inv.app A ≫
    (derivedPullback (pullback.snd g' U.ι)).map
      ((relativeMVComp U.ι f).inv.app A ≫ (derivedPullback U.ι).map a)
  have hp' :
      (relativeMVComp (pullback.fst g' U.ι) f').inv.app ((derivedPullback g).obj A) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((relativeMVComp f' g).hom.app A ≫
            eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A) hpull.w.symm) ≫
            (relativeMVComp g' f).inv.app A ≫ (derivedPullback g').map a) =
      r ≫ d.hom.app C := by
    simpa only [r, d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Category.assoc] using hp
  have h := congrArg (fun t ↦
    (relativeMVComp (pullback.fst g' U.ι) f').hom.app ((derivedPullback g).obj A) ≫
      t ≫ d.inv.app C ≫
      (derivedPullback (pullback.snd g' U.ι)).map ((relativeMVAdj U.ι).counit.app E) ≫
      d.hom.app K) hp'
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at h
  simpa only [r, d, a, A, C, E, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
    Functor.map_comp, Category.assoc] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The composite base-change transpose before applying the target open counit.
Source: Stacks Project, Cohomology, Tags 08HY, 08HZ and 0D5S.
(blueprint: new-relative-mv-composite-base-change-prefix).
Proof: Expand the U local arrow. The mate equation for the inverse U,f direct-image
comparison and naturality of the composite adjunction counit express its f'-transpose
as base change for f, followed by base change for U and the U coefficient comparison.
The composite counit formula pulls the f counit through the U comparison; triangle
identities cancel the intermediate f'-unit. Pull this formula back along W' to X'.
Apply associativity coherence of the canonical pullback comparisons to W→X→S and
the corresponding pullback squares. The projection identities and hpull.w identify
all composite scheme morphisms, and proof irrelevance identifies transports. This
leaves exactly the W square comparison and pulled-back f counit, the W coefficient
comparison at C, and the pulled-back U base-change arrow. No counit for U'→X'
is computed or applied. All identities include equal and empty opens and zero
complexes, since they are natural transformations and coherence identities. -/
theorem relativeMV_composite_baseChange_prefix
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (W U : X.Opens) :
    let C := (schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)
    let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj ((derivedPullback U.ι).obj K)
    let θ := (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' U.ι) g').inv.app K
    (relativeMVComp (pullback.fst g' W.ι) f').inv.app
      (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) U).left ≫
      (derivedPullback (pullback.fst g' W.ι)).map
        (((relativeMVAdj f').homEquiv _ _).symm
          ((relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
              (𝟙 _) U).hom ≫
            (relativeMVImageComp (pullback.fst g' U.ι) f').inv.app
              ((derivedPullback (pullback.fst g' U.ι)).obj
                ((derivedPullback g').obj K)))) =
      (relativeMVComp (pullback.fst g' W.ι ≫ f') g).hom.app A ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A)
        (show pullback.snd g' W.ι ≫ (W.ι ≫ f) =
            (pullback.fst g' W.ι ≫ f') ≫ g by
          rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]).symm) ≫
      (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).inv.app A ≫
      (derivedPullback (pullback.snd g' W.ι)).map
        ((relativeMVComp W.ι f).inv.app A ≫
          (derivedPullback W.ι).map
            ((derivedPullback f).map ((relativeMVImageComp U.ι f).inv.app
                ((derivedPullback U.ι).obj K)) ≫ (relativeMVAdj f).counit.app C)) ≫
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app C ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj C)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app C ≫
      (derivedPullback (pullback.fst g' W.ι)).map
        (schemeDerivedBaseChangeMap U.ι (pullback.fst g' U.ι) g'
            (pullback.snd g' U.ι) (pullback.condition (f := g') (g := U.ι)).symm
            ((derivedPullback U.ι).obj K) ≫
          (schemeDerivedDirectImage (pullback.fst g' U.ι)).map θ) := by
  dsimp only
  rw [local_transpose]
  let E := (derivedPullback U.ι).obj K
  let C := (schemeDerivedDirectImage U.ι).obj E
  let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj E
  let a := (derivedPullback f).map ((relativeMVImageComp U.ι f).inv.app E) ≫
    (relativeMVAdj f).counit.app C
  let θ := (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := U.ι)).symm) ≫
    (relativeMVComp (pullback.fst g' U.ι) g').inv.app K
  let b := schemeDerivedBaseChangeMap U.ι (pullback.fst g' U.ι) g'
    (pullback.snd g' U.ι) (pullback.condition (f := g') (g := U.ι)).symm E ≫
    (schemeDerivedDirectImage (pullback.fst g' U.ι)).map θ
  have h := square_factor f f' g g' hpull A C a W
  simpa only [a, b, θ, A, C, E, relativeMVLocalArrow, Arrow.mk_left,
    Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ (derivedPullback (pullback.fst g' W.ι)).map b) h

end AlgebraicGeometry
