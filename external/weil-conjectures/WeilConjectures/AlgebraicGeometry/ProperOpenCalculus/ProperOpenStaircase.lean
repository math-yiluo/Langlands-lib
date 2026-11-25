/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenCalculus

/-!
# Coherence on a supplied proper/open staircase

## References

* Stacks Project, Tag 0F7K
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperOpenCalculus

/-- The two compositions on one supplied staircase agree. -/
theorem properOpen_staircase {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A)
    (X Y Z W : {X : Scheme.{u} // A X})
      (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
      [QuasiCompact f]
      [QuasiCompact g]
      [QuasiCompact h]
      (T : Compactification.Tower f g h) (hT : TowerObjects (A := A) T) :
      Functor.whiskerRight
          (F.towerIso X Y Z T.fg ⟨hT.1, hT.2.1, hT.2.2.2.1⟩).hom
          (F.H Z W T.ch hT.2.2.1) ≫
          (F.towerIso X Z W T.fg_h ⟨hT.2.2.2.1, hT.2.2.1, hT.2.2.2.2.2⟩).hom =
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (F.H X Y T.cf hT.1)
            (F.towerIso Y Z W T.gh ⟨hT.2.1, hT.2.2.1, hT.2.2.2.2.1⟩).hom ≫
          (F.towerIso X Y W T.f_gh ⟨hT.1, hT.2.2.2.2.1, hT.2.2.2.2.2⟩).hom  := by
  have : QuasiCompact T.cf.i := T.cf.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.ch.i := T.ch.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.cfg.i := T.cfg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.cgh.i := T.cgh.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.cfgh.i := T.cfgh.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.q := MorphismProperty.of_isPullback T.isPullback_fg
    (inferInstance : QuasiCompact T.cg.i)
  have : QuasiCompact T.q₂ := MorphismProperty.of_isPullback T.isPullback_gh
    (inferInstance : QuasiCompact T.ch.i)
  have : QuasiCompact T.q' := MorphismProperty.of_isPullback T.isPullback_mid
    (inferInstance : QuasiCompact T.q₂)
  have : IsProper T.p := Compactification.Triangle.isProper_p T.fg
  have : IsProper T.p₂ := Compactification.Triangle.isProper_p T.gh
  have : IsProper T.p₁ := Compactification.Triangle.isProper_p T.f_gh
  let U : {X : Scheme.{u} // A X} := ⟨T.cf.Z, hT.1⟩
  let V : {X : Scheme.{u} // A X} := ⟨T.cfg.Z, hT.2.2.2.1⟩
  let E : {X : Scheme.{u} // A X} := ⟨T.cfgh.Z, hT.2.2.2.2.2⟩
  let B : {X : Scheme.{u} // A X} := ⟨T.cg.Z, hT.2.1⟩
  let D : {X : Scheme.{u} // A X} := ⟨T.cgh.Z, hT.2.2.2.2.1⟩
  let C : {X : Scheme.{u} // A X} := ⟨T.ch.Z, hT.2.2.1⟩
  let ga := F.gamma U V Y B T.q T.cf.g T.p T.cg.i T.isPullback_fg.w.symm
  let gb := F.gamma V E B D T.q' T.p T.p₁ T.q₂ T.isPullback_mid.w.symm
  let gc := F.gamma B D Z C T.q₂ T.cg.g T.p₂ T.ch.i T.isPullback_gh.w.symm
  let gv := F.gamma V E Z C T.q' T.cfg.g (T.p₁ ≫ T.p₂) T.ch.i
    T.fg_h.isPullback.w.symm
  let gh := F.gamma U E Y D (T.q ≫ T.q') T.cf.g T.p₁ T.cgh.i
    T.f_gh.isPullback.w.symm
  let a := F.jComp X U V T.cf.i T.q T.cfg.i T.i_q
  let b := F.jComp X V E T.cfg.i T.q' T.cfgh.i T.i_q'
  let c := F.jComp Y B D T.cg.i T.q₂ T.cgh.i T.i_q₂
  let d := F.jComp X U E T.cf.i (T.q ≫ T.q') T.cfgh.i T.f_gh.i_q
  let e := F.jComp U V E T.q T.q' (T.q ≫ T.q') rfl
  let l := F.pComp V B Z T.p T.cg.g T.cfg.g T.p_g
  let m := F.pComp D C W T.p₂ T.ch.g T.cgh.g T.p₂_g
  let n := F.pComp E C W (T.p₁ ≫ T.p₂) T.ch.g T.cfgh.g T.fg_h.p_g
  let o := F.pComp E D W T.p₁ T.cgh.g T.cfgh.g T.p₁_g
  let z := F.pComp E D C T.p₁ T.p₂ (T.p₁ ≫ T.p₂) rfl
  have hv (N : F.obj V) :
      (F.J Z C T.ch.i).map (l.hom.app N) ≫ gv.hom.app N ≫
        z.inv.app ((F.J V E T.q').obj N) =
      gc.hom.app ((F.P V B T.p).obj N) ≫
        (F.P D C T.p₂).map (gb.hom.app N) := by
    have hv₀ := F.vertical V E B D Z C T.q' T.q₂ T.ch.i T.p T.cg.g T.p₁ T.p₂
      T.isPullback_mid.w.symm T.isPullback_gh.w.symm
      (by rw [← Category.assoc, T.isPullback_mid.w.symm, Category.assoc,
        T.isPullback_gh.w.symm, Category.assoc]) N
    have transport (pg : V.1 ⟶ Z.1) [IsProper pg] (hp : T.p ≫ T.cg.g = pg) :
        (F.J Z C T.ch.i).map ((F.pComp V B Z T.p T.cg.g pg hp).hom.app N) ≫
          (F.gamma V E Z C T.q' pg (T.p₁ ≫ T.p₂) T.ch.i
            ((show T.q' ≫ (T.p₁ ≫ T.p₂) = (T.p ≫ T.cg.g) ≫ T.ch.i by
              rw [← Category.assoc, T.isPullback_mid.w.symm, Category.assoc,
              T.isPullback_gh.w.symm, Category.assoc]).trans
              (congrArg (fun t ↦ t ≫ T.ch.i) hp))).hom.app N ≫
          z.inv.app ((F.J V E T.q').obj N) =
        gc.hom.app ((F.P V B T.p).obj N) ≫
          (F.P D C T.p₂).map (gb.hom.app N) := by
      subst pg
      exact hv₀
    exact transport T.cfg.g T.p_g
  have hh (N : F.obj U) :
      c.hom.app ((F.P U Y T.cf.g).obj N) ≫ gh.hom.app N ≫
        (F.P E D T.p₁).map (e.inv.app N) =
      (F.J B D T.q₂).map (ga.hom.app N) ≫
        gb.hom.app ((F.J U V T.q).obj N) := by
    have hh₀ := F.horizontal U V E Y B D T.q T.q' T.cg.i T.q₂ T.cf.g T.p T.p₁
      T.isPullback_fg.w.symm T.isPullback_mid.w.symm
      (by rw [Category.assoc, T.isPullback_mid.w.symm, ← Category.assoc,
        T.isPullback_fg.w.symm, Category.assoc]) N
    have transport (ij : Y.1 ⟶ D.1) [IsOpenImmersion ij] [QuasiCompact ij]
        (hi : T.cg.i ≫ T.q₂ = ij) :
        (F.jComp Y B D T.cg.i T.q₂ ij hi).hom.app ((F.P U Y T.cf.g).obj N) ≫
          (F.gamma U E Y D (T.q ≫ T.q') T.cf.g T.p₁ ij
            ((show (T.q ≫ T.q') ≫ T.p₁ = T.cf.g ≫ (T.cg.i ≫ T.q₂) by
              rw [Category.assoc, T.isPullback_mid.w.symm, ← Category.assoc,
              T.isPullback_fg.w.symm, Category.assoc]).trans
              (congrArg (fun t ↦ T.cf.g ≫ t) hi))).hom.app N ≫
          (F.P E D T.p₁).map (e.inv.app N) =
        (F.J B D T.q₂).map (ga.hom.app N) ≫
          gb.hom.app ((F.J U V T.q).obj N) := by
      subst ij
      exact hh₀
    exact transport T.cgh.i T.i_q₂
  have hv' (N : F.obj V) :
      (F.J Z C T.ch.i).map (l.hom.app N) ≫ gv.hom.app N =
      gc.hom.app ((F.P V B T.p).obj N) ≫
        (F.P D C T.p₂).map (gb.hom.app N) ≫
        z.hom.app ((F.J V E T.q').obj N) := by
    apply (cancel_mono (z.inv.app ((F.J V E T.q').obj N))).mp
    simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id] using hv N
  have hh' (N : F.obj U) :
      c.hom.app ((F.P U Y T.cf.g).obj N) ≫ gh.hom.app N =
      (F.J B D T.q₂).map (ga.hom.app N) ≫
        gb.hom.app ((F.J U V T.q).obj N) ≫ (F.P E D T.p₁).map (e.hom.app N) := by
    apply (cancel_mono ((F.P E D T.p₁).map (e.inv.app N))).mp
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact hh N
  have core (N : F.obj U) :
      (F.J Z C T.ch.i).map ((F.P B Z T.cg.g).map (ga.hom.app N)) ≫
        (F.J Z C T.ch.i).map (l.hom.app ((F.J U V T.q).obj N)) ≫
        gv.hom.app ((F.J U V T.q).obj N) ≫
        (F.P E C (T.p₁ ≫ T.p₂)).map (e.hom.app N) =
      gc.hom.app ((F.J Y B T.cg.i).obj ((F.P U Y T.cf.g).obj N)) ≫
        (F.P D C T.p₂).map (c.hom.app ((F.P U Y T.cf.g).obj N)) ≫
        (F.P D C T.p₂).map (gh.hom.app N) ≫
        z.hom.app ((F.J U E (T.q ≫ T.q')).obj N) := by
    have hn := gc.hom.naturality (ga.hom.app N)
    have hz := z.hom.naturality (e.hom.app N)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn hz
    rw [← Category.assoc ((F.J Z C T.ch.i).map (l.hom.app _)), hv']
    simp only [Category.assoc]
    rw [← Category.assoc ((F.J Z C T.ch.i).map _), hn]
    simp only [Category.assoc]
    rw [← hz]
    simp only [← Category.assoc, ← Functor.map_comp]
    simp only [Category.assoc]
    rw [← hh']
  ext M
  dsimp only [towerIso, H, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator, Functor.comp_map, Functor.comp_obj]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  change
    (F.P C W T.ch.g).map ((F.J Z C T.ch.i).map
      ((F.P B Z T.cg.g).map (ga.hom.app ((F.J X U T.cf.i).obj M)))) ≫
    (F.P C W T.ch.g).map ((F.J Z C T.ch.i).map
      ((F.P B Z T.cg.g).map ((F.P V B T.p).map (a.hom.app M)))) ≫
    (F.P C W T.ch.g).map ((F.J Z C T.ch.i).map
      (l.hom.app ((F.J X V T.cfg.i).obj M))) ≫
    (F.P C W T.ch.g).map (gv.hom.app ((F.J X V T.cfg.i).obj M)) ≫
    (F.P C W T.ch.g).map ((F.P E C (T.p₁ ≫ T.p₂)).map (b.hom.app M)) ≫
    n.hom.app ((F.J X E T.cfgh.i).obj M) =
    (F.P C W T.ch.g).map (gc.hom.app
      ((F.J Y B T.cg.i).obj ((F.P U Y T.cf.g).obj ((F.J X U T.cf.i).obj M)))) ≫
    (F.P C W T.ch.g).map ((F.P D C T.p₂).map (c.hom.app
      ((F.P U Y T.cf.g).obj ((F.J X U T.cf.i).obj M)))) ≫
    m.hom.app ((F.J Y D T.cgh.i).obj
      ((F.P U Y T.cf.g).obj ((F.J X U T.cf.i).obj M))) ≫
    (F.P D W T.cgh.g).map (gh.hom.app ((F.J X U T.cf.i).obj M)) ≫
    (F.P D W T.cgh.g).map ((F.P E D T.p₁).map (d.hom.app M)) ≫
    o.hom.app ((F.J X E T.cfgh.i).obj M)
  have hn₁ := m.hom.naturality (gh.hom.app ((F.J X U T.cf.i).obj M))
  have hn₂ := m.hom.naturality ((F.P E D T.p₁).map (d.hom.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₁ hn₂
  rw [← Category.assoc (m.hom.app _), ← hn₁]
  simp only [Category.assoc]
  rw [← Category.assoc (m.hom.app _), ← hn₂]
  simp only [Category.assoc]
  rw [← F.pAssoc E D C W T.p₁ T.p₂ T.ch.g (T.p₁ ≫ T.p₂) T.cgh.g T.cfgh.g
    rfl T.p₂_g T.fg_h.p_g T.p₁_g]
  simp only [← Category.assoc]
  apply (cancel_mono (n.hom.app ((F.J X E T.cfgh.i).obj M))).mpr
  simp only [← Functor.map_comp]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  have hl := l.hom.naturality (a.hom.app M)
  have hg := gv.hom.naturality (a.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hl hg
  have hl' := congrArg (F.J Z C T.ch.i).map hl
  simp only [Functor.map_comp] at hl'
  rw [← Category.assoc ((F.J Z C T.ch.i).map
    ((F.P B Z T.cg.g).map ((F.P V B T.p).map (a.hom.app M)))), hl']
  simp only [Category.assoc]
  rw [← Category.assoc ((F.J Z C T.ch.i).map
    ((F.P V Z T.cfg.g).map (a.hom.app M))), hg]
  simp only [Category.assoc]
  rw [← Functor.map_comp (F.P E C (T.p₁ ≫ T.p₂))]
  rw [F.jAssoc X U V E T.cf.i T.q T.q' T.cfg.i (T.q ≫ T.q') T.cfgh.i
    T.i_q rfl T.i_q' T.f_gh.i_q]
  simp only [Functor.map_comp]
  have coreM := core ((F.J X U T.cf.i).obj M)
  simp only [← Category.assoc] at coreM ⊢
  rw [coreM]
  simp only [Category.assoc]
  have hz := z.hom.naturality (d.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hz
  rw [← hz]

end AlgebraicGeometry.ProperOpenCalculus
