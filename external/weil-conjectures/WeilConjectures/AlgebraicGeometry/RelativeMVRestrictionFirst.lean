/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.CoefficientSquarePasting

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Elaborating the fixed derived adjunction data needs a larger budget.
private theorem unit_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {A X S : Scheme.{u}} (j : A ⟶ X) (f : X ⟶ S)
    (K : schemeDerivedCategory X) :
    ((relativeMVAdj (j ≫ f)).homEquiv _ _).symm (relativeMVUnit j f K) =
      (relativeMVComp j f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
        (derivedPullback j).map ((relativeMVAdj f).counit.app K) := by
  unfold relativeMVUnit relativeMVImageComp
  rw [Adjunction.homEquiv_naturality_left_symm]
  dsimp only [Functor.comp_obj]
  have hc := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (((relativeMVAdj f).comp (relativeMVAdj j)).ofNatIsoLeft (relativeMVComp j f))
    (relativeMVAdj (j ≫ f)) ((derivedPullback j).obj K)
  dsimp only [Functor.comp_obj] at hc
  rw [hc]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_counit_app]
  dsimp only [Functor.comp_obj]
  have hn := (relativeMVComp j f).inv.naturality
    ((schemeDerivedDirectImage f).map ((relativeMVAdj j).unit.app K))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have hn := (relativeMVAdj f).counit.naturality ((relativeMVAdj j).unit.app K)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  simp only [Functor.map_comp, Category.assoc]
  simp


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
private theorem localArrow_factor
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W : X.Opens) :
    (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom =
      (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) W).hom ≫
        (schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).map
          ((derivedPullback (pullback.fst g' W.ι)).map φ) := by
  simp only [relativeMVLocalArrow, Arrow.mk_hom, Functor.map_comp, Category.assoc]
  rw [(derivedPullback (pullback.fst g' W.ι)).map_id]
  erw [(schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).map_id]
  simp only [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_coefficients
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {A X S : Scheme.{u}} (j : A ⟶ X) (f : X ⟶ S)
    {K L : schemeDerivedCategory X} (ψ : K ⟶ L) :
    (schemeDerivedDirectImage f).map ψ ≫ relativeMVUnit j f L =
      relativeMVUnit j f K ≫
        (schemeDerivedDirectImage (j ≫ f)).map ((derivedPullback j).map ψ) := by
  unfold relativeMVUnit
  simp only [← Category.assoc, ← Functor.map_comp]
  have hn := (relativeMVAdj j).unit.naturality ψ
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [hn]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (relativeMVImageComp j f).hom.naturality ((derivedPullback j).map ψ)
  dsimp only [Functor.comp_map] at hn
  rw [hn]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The comparison data in the transpose require a larger elaboration budget.
private theorem source_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g) (K : schemeDerivedCategory X) (W : X.Opens) :
    let A := (schemeDerivedDirectImage f).obj K
    let t := (relativeMVComp (pullback.fst g' W.ι ≫ f') g).hom.app A ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A)
        (show pullback.snd g' W.ι ≫ (W.ι ≫ f) =
            (pullback.fst g' W.ι ≫ f') ≫ g by
          rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]).symm) ≫
      (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).inv.app A ≫
      (derivedPullback (pullback.snd g' W.ι)).map
        ((relativeMVComp W.ι f).inv.app A ≫
          (derivedPullback W.ι).map ((relativeMVAdj f).counit.app K)) ≫
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app K
    ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm
      ((derivedPullback g).map (relativeMVUnit W.ι f K) ≫
        (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
          (𝟙 _) W).hom) = t := by
  dsimp only
  simp only [relativeMVLocalArrow, Arrow.mk_hom]
  rw [(derivedPullback (pullback.fst g' W.ι)).map_id]
  erw [Category.comp_id]
  rw [← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm, baseChange_counit]
  let h : pullback.snd g' W.ι ≫ (W.ι ≫ f) =
      (pullback.fst g' W.ι ≫ f') ≫ g := by
    rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]
  let c := relativeMVComp (pullback.fst g' W.ι ≫ f') g ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫
    (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).symm
  have hn := c.hom.naturality (relativeMVUnit W.ι f K)
  simp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Functor.comp_obj, Functor.comp_map] at hn
  simp only [Category.assoc] at hn ⊢
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc]
  have hc := unit_counit W.ι f K
  change (derivedPullback (W.ι ≫ f)).map (relativeMVUnit W.ι f K) ≫
    (relativeMVAdj (W.ι ≫ f)).counit.app ((derivedPullback W.ι).obj K) = _ at hc
  rw [hc]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The comparison data in the transpose require a larger elaboration budget.
private theorem target_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g) (K : schemeDerivedCategory X) (W : X.Opens) :
    let A := (schemeDerivedDirectImage f).obj K
    ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm
      ((relativeMVGlobalArrow f f' g g' hpull K ((derivedPullback g').obj K)
          (𝟙 _)).hom ≫
        relativeMVUnit (pullback.fst g' W.ι) f' ((derivedPullback g').obj K)) =
      (relativeMVComp (pullback.fst g' W.ι) f').inv.app ((derivedPullback g).obj A) ≫
        (derivedPullback (pullback.fst g' W.ι)).map
          ((relativeMVComp f' g).hom.app A ≫
            eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A) hpull.w.symm) ≫
            (relativeMVComp g' f).inv.app A ≫
            (derivedPullback g').map ((relativeMVAdj f).counit.app K)) := by
  dsimp only
  simp only [relativeMVGlobalArrow, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right]
  rw [(schemeDerivedDirectImage f').map_id, Category.comp_id]
  rw [Adjunction.homEquiv_naturality_left_symm, unit_counit]
  have hn := (relativeMVComp (pullback.fst g' W.ι) f').inv.naturality
    (schemeDerivedBaseChangeMap f f' g g' hpull.w K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  have hc := baseChange_counit f f' g g' hpull.w K
  change (derivedPullback f').map (schemeDerivedBaseChangeMap f f' g g' hpull.w K) ≫
    (relativeMVAdj f').counit.app ((derivedPullback g').obj K) = _ at hc
  rw [hc]

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
-- Transposing the fixed derived adjunction data needs a larger elaboration budget.
/-- Base change commutes with the relative unit of one open.
Source: Stacks Project, Cohomology, Tags 08HY and 08HZ.
(blueprint: new-relative-mv-first).
Proof: Transpose the two paths under the adjunction for the inverse-image open
followed by f'. Expand base change as the transpose of the pulled-back counit.
The unit of the composite adjunction and the right-adjoint mate defining
relativeMVImageComp cancel by the triangle identities. The pullback composition
coherence identifies the two remaining comparisons, using the pullback
projection equality. Naturality of the counit moves the object map φ through
the comparison. Both paths therefore have the same transpose. This works for
all opens, including the empty open, and for arbitrary φ. -/
theorem relativeMV_restriction_unit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W : X.Opens) :
    (derivedPullback g).map (relativeMVUnit W.ι f K) ≫
      (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom =
      (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom ≫
        relativeMVUnit (pullback.fst g' W.ι) f' K' := by
  rw [localArrow_factor f f' g g' hpull K K' φ W]
  have hc :
      (derivedPullback g).map (relativeMVUnit W.ι f K) ≫
          (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
            (𝟙 _) W).hom =
        (relativeMVGlobalArrow f f' g g' hpull K ((derivedPullback g').obj K)
          (𝟙 _)).hom ≫
          relativeMVUnit (pullback.fst g' W.ι) f' ((derivedPullback g').obj K) := by
    apply ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm.injective
    rw [source_counit]
    erw [target_counit f f' g g' hpull K W]
    let d := relativeMVComp (pullback.snd g' W.ι) W.ι ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k)
        (pullback.condition (f := g') (g := W.ι)).symm) ≪≫
      (relativeMVComp (pullback.fst g' W.ι) g').symm
    have hn := d.hom.naturality ((relativeMVAdj f).counit.app K)
    simp only [d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app, Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hn
    have hpast := comparison_pasting f f' g g' hpull
      ((schemeDerivedDirectImage f).obj K) W
    simp only [Functor.mapIso_hom, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.comp_obj,
      Functor.map_comp, Category.assoc] at hpast hn ⊢
    rw [hn]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ (derivedPullback (pullback.fst g' W.ι)).map
        ((derivedPullback g').map ((relativeMVAdj f).counit.app K))) hpast
  have hn := unit_coefficients (pullback.fst g' W.ι) f' φ
  simp only [← Category.assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [← hn]
  simp only [relativeMVGlobalArrow, Arrow.mk_hom]
  rw [(schemeDerivedDirectImage f').map_id]
  simp only [Category.comp_id, Category.assoc]

end AlgebraicGeometry
