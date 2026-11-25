/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenCalculus

/-!
# Naturality on a single refining tower

## References

* Stacks Project, Tag 0F7J, six-square calculation
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperOpenCalculus

/-- A single refining binary tower commutes with its three refinement isomorphisms. -/
theorem properOpen_tower_refinement {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A)
    (X Y Z : {X : Scheme.{u} // A X})
    {f : X.1 ⟶ Y.1} {g : Y.1 ⟶ Z.1} [QuasiCompact f] [QuasiCompact g]
    (T R : Compactification.Triangle f g)
    (hT : TriangleObjects (A := A) T) (hR : TriangleObjects (A := A) R)
    (r : TowerRefinement R T) :
    (F.towerIso X Y Z T hT).hom ≫ (F.rho X Z hT.2.2 hR.2.2 r.rfg).hom =
      NatTrans.hcomp (F.rho X Y hT.1 hR.1 r.rf).hom
        (F.rho Y Z hT.2.1 hR.2.1 r.rg).hom ≫ (F.towerIso X Y Z R hR).hom := by
  have : QuasiCompact T.cf.i := T.cf.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.cfg.i := T.cfg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact R.cf.i := R.cf.quasiCompact_openImmersion inferInstance
  have : QuasiCompact R.cg.i := R.cg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact R.cfg.i := R.cfg.quasiCompact_openImmersion inferInstance
  have : QuasiCompact T.q := MorphismProperty.of_isPullback T.isPullback
    (inferInstance : QuasiCompact T.cg.i)
  have : QuasiCompact R.q := MorphismProperty.of_isPullback R.isPullback
    (inferInstance : QuasiCompact R.cg.i)
  let U : {X : Scheme.{u} // A X} := ⟨T.cf.Z, hT.1⟩
  let V : {X : Scheme.{u} // A X} := ⟨T.cfg.Z, hT.2.2⟩
  let B : {X : Scheme.{u} // A X} := ⟨T.cg.Z, hT.2.1⟩
  let U' : {X : Scheme.{u} // A X} := ⟨R.cf.Z, hR.1⟩
  let V' : {X : Scheme.{u} // A X} := ⟨R.cfg.Z, hR.2.2⟩
  let B' : {X : Scheme.{u} // A X} := ⟨R.cg.Z, hR.2.1⟩
  let ga := F.gamma X U' X U R.cf.i (𝟙 X.1) r.rf.hom T.cf.i
    (r.rf.i_hom.trans (Category.id_comp _).symm)
  let gd := F.gamma Y B' Y B R.cg.i (𝟙 Y.1) r.rg.hom T.cg.i
    (r.rg.i_hom.trans (Category.id_comp _).symm)
  let ge := F.gamma X V' X V R.cfg.i (𝟙 X.1) r.rfg.hom T.cfg.i
    (r.rfg.i_hom.trans (Category.id_comp _).symm)
  let gf := F.gamma U' V' U V R.q r.rf.hom r.rfg.hom T.q r.q_comm
  let gb := F.gamma U V Y B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm
  let gc := F.gamma U' V' Y B' R.q R.cf.g R.p R.cg.i R.isPullback.w.symm
  let aT := F.jComp X U V T.cf.i T.q T.cfg.i T.i_q
  let ar := F.jComp X U' V' R.cf.i R.q R.cfg.i R.i_q
  let pt := F.pComp U' U Y r.rf.hom T.cf.g R.cf.g r.rf.hom_g
  let kh := F.pComp V' V B r.rfg.hom T.p (r.rfg.hom ≫ T.p) rfl
  let kd := F.pComp V' B' B R.p r.rg.hom (r.rfg.hom ≫ T.p) r.p_comm.symm
  let gg := F.gamma U' V' Y B R.q R.cf.g (r.rfg.hom ≫ T.p) T.cg.i
    (by rw [r.p_comm, ← Category.assoc, R.isPullback.w.symm,
      Category.assoc, r.rg.i_hom])
  have hh (M : F.obj X) :
      aT.hom.app ((F.P X X (𝟙 X.1)).obj M) ≫ ge.hom.app M ≫
        (F.P V' V r.rfg.hom).map (ar.inv.app M) =
      (F.J U V T.q).map (ga.hom.app M) ≫ gf.hom.app ((F.J X U' R.cf.i).obj M) := by
    have hh₀ := F.horizontal X U' V' X U V R.cf.i R.q T.cf.i T.q
      (𝟙 X.1) r.rf.hom r.rfg.hom
      (r.rf.i_hom.trans (Category.id_comp _).symm) r.q_comm
      (by rw [Category.assoc, r.q_comm, ← Category.assoc, r.rf.i_hom,
        Category.id_comp]) M
    have transport (i : X.1 ⟶ V.1) (j : X.1 ⟶ V'.1)
        [IsOpenImmersion i] [QuasiCompact i] [IsOpenImmersion j] [QuasiCompact j]
        (hi : T.cf.i ≫ T.q = i) (hj : R.cf.i ≫ R.q = j) :
        (F.jComp X U V T.cf.i T.q i hi).hom.app ((F.P X X (𝟙 X.1)).obj M) ≫
          (F.gamma X V' X V j (𝟙 X.1) r.rfg.hom i
            (by rw [← hi, ← hj, Category.assoc, r.q_comm,
              ← Category.assoc, r.rf.i_hom, Category.id_comp])).hom.app M ≫
          (F.P V' V r.rfg.hom).map
            ((F.jComp X U' V' R.cf.i R.q j hj).inv.app M) =
        (F.J U V T.q).map (ga.hom.app M) ≫
          gf.hom.app ((F.J X U' R.cf.i).obj M) := by
      subst i
      subst j
      exact hh₀
    exact transport T.cfg.i R.cfg.i T.i_q R.i_q
  have hv₁ (N : F.obj U') :
      (F.J Y B T.cg.i).map (pt.hom.app N) ≫ gg.hom.app N ≫
        kh.inv.app ((F.J U' V' R.q).obj N) =
      gb.hom.app ((F.P U' U r.rf.hom).obj N) ≫
        (F.P V B T.p).map (gf.hom.app N) := by
    have hv₀ := F.vertical U' V' U V Y B R.q T.q T.cg.i r.rf.hom T.cf.g
      r.rfg.hom T.p r.q_comm T.isPullback.w.symm
      (by rw [← Category.assoc, r.q_comm, Category.assoc,
        T.isPullback.w.symm, Category.assoc]) N
    have transport (p : U'.1 ⟶ Y.1) [IsProper p] (hp : r.rf.hom ≫ T.cf.g = p) :
        (F.J Y B T.cg.i).map ((F.pComp U' U Y r.rf.hom T.cf.g p hp).hom.app N) ≫
          (F.gamma U' V' Y B R.q p (r.rfg.hom ≫ T.p) T.cg.i
            (by rw [← hp, ← Category.assoc, r.q_comm, Category.assoc,
              T.isPullback.w.symm, Category.assoc])).hom.app N ≫
          kh.inv.app ((F.J U' V' R.q).obj N) =
        gb.hom.app ((F.P U' U r.rf.hom).obj N) ≫
          (F.P V B T.p).map (gf.hom.app N) := by
      subst p
      exact hv₀
    exact transport R.cf.g r.rf.hom_g
  have hv₂ (N : F.obj U') :
      (F.J Y B T.cg.i).map ((F.pId Y).hom.app ((F.P U' Y R.cf.g).obj N)) ≫
          gg.hom.app N ≫ kd.inv.app ((F.J U' V' R.q).obj N) =
        gd.hom.app ((F.P U' Y R.cf.g).obj N) ≫
          (F.P B' B r.rg.hom).map (gc.hom.app N) := by
    have hv₀ := F.vertical U' V' Y B' Y B R.q R.cg.i T.cg.i R.cf.g (𝟙 Y.1)
      R.p r.rg.hom R.isPullback.w.symm
      (r.rg.i_hom.trans (Category.id_comp _).symm)
      (by rw [← Category.assoc, R.isPullback.w.symm, Category.assoc,
        r.rg.i_hom, Category.comp_id]) N
    have transport (p : U'.1 ⟶ Y.1) (q : V'.1 ⟶ B.1)
        [IsProper p] [IsProper q] (hp : R.cf.g ≫ 𝟙 Y.1 = p)
        (hq : R.p ≫ r.rg.hom = q) :
        (F.J Y B T.cg.i).map
            ((F.pComp U' Y Y R.cf.g (𝟙 Y.1) p hp).hom.app N) ≫
          (F.gamma U' V' Y B R.q p q T.cg.i
            (by rw [← hp, ← hq, ← Category.assoc, R.isPullback.w.symm,
              Category.assoc, r.rg.i_hom, Category.comp_id])).hom.app N ≫
          (F.pComp V' B' B R.p r.rg.hom q hq).inv.app ((F.J U' V' R.q).obj N) =
        gd.hom.app ((F.P U' Y R.cf.g).obj N) ≫
          (F.P B' B r.rg.hom).map (gc.hom.app N) := by
      subst p
      subst q
      exact hv₀
    simpa only [F.pRight] using
      transport R.cf.g (r.rfg.hom ≫ T.p) (Category.comp_id _) r.p_comm.symm
  let ta (M : F.obj X) := (F.J X U T.cf.i).map ((F.pId X).inv.app M) ≫ ga.hom.app M
  let td (N : F.obj Y) := (F.J Y B T.cg.i).map ((F.pId Y).inv.app N) ≫ gd.hom.app N
  let te (M : F.obj X) := (F.J X V T.cfg.i).map ((F.pId X).inv.app M) ≫ ge.hom.app M
  have hh' (M : F.obj X) :
      aT.hom.app M ≫ te M =
        (F.J U V T.q).map (ta M) ≫ gf.hom.app ((F.J X U' R.cf.i).obj M) ≫
          (F.P V' V r.rfg.hom).map (ar.hom.app M) := by
    have hh₁ : aT.hom.app M ≫ te M ≫
        (F.P V' V r.rfg.hom).map (ar.inv.app M) =
        (F.J U V T.q).map (ta M) ≫ gf.hom.app ((F.J X U' R.cf.i).obj M) := by
      dsimp only [te, ta]
      have hn := aT.hom.naturality ((F.pId X).inv.app M)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      simp only [← Category.assoc]
      rw [← hn]
      simp only [Category.assoc]
      rw [hh]
      simp only [Functor.map_comp, Category.assoc]
    apply (cancel_mono ((F.P V' V r.rfg.hom).map (ar.inv.app M))).mp
    simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id] using hh₁
  have hv₂' (N : F.obj U') :
      gg.hom.app N = td ((F.P U' Y R.cf.g).obj N) ≫
        (F.P B' B r.rg.hom).map (gc.hom.app N) ≫
          kd.hom.app ((F.J U' V' R.q).obj N) := by
    apply (cancel_epi ((F.J Y B T.cg.i).map
      ((F.pId Y).hom.app ((F.P U' Y R.cf.g).obj N)))).mp
    apply (cancel_mono (kd.inv.app ((F.J U' V' R.q).obj N))).mp
    dsimp only [td]
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.id_obj, CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using hv₂ N
  have hv (N : F.obj U') :
      gb.hom.app ((F.P U' U r.rf.hom).obj N) ≫
        (F.P V B T.p).map (gf.hom.app N) ≫
          kh.hom.app ((F.J U' V' R.q).obj N) =
      (F.J Y B T.cg.i).map (pt.hom.app N) ≫ td ((F.P U' Y R.cf.g).obj N) ≫
        (F.P B' B r.rg.hom).map (gc.hom.app N) ≫
          kd.hom.app ((F.J U' V' R.q).obj N) := by
    rw [← hv₂']
    apply (cancel_mono (kh.inv.app ((F.J U' V' R.q).obj N))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
    exact (hv₁ N).symm
  have core (M : F.obj X) :
      gb.hom.app ((F.J X U T.cf.i).obj M) ≫
        (F.P V B T.p).map (aT.hom.app M) ≫ (F.P V B T.p).map (te M) ≫
          kh.hom.app ((F.J X V' R.cfg.i).obj M) =
      (F.J Y B T.cg.i).map ((F.P U Y T.cf.g).map (ta M)) ≫
        (F.J Y B T.cg.i).map (pt.hom.app ((F.J X U' R.cf.i).obj M)) ≫
        td ((F.P U' Y R.cf.g).obj ((F.J X U' R.cf.i).obj M)) ≫
        (F.P B' B r.rg.hom).map (gc.hom.app ((F.J X U' R.cf.i).obj M)) ≫
        (F.P B' B r.rg.hom).map ((F.P V' B' R.p).map (ar.hom.app M)) ≫
          kd.hom.app ((F.J X V' R.cfg.i).obj M) := by
    rw [← Category.assoc ((F.P V B T.p).map _), ← Functor.map_comp, hh']
    simp only [Functor.map_comp, Category.assoc]
    have hn := gb.hom.naturality (ta M)
    have hk := kh.hom.naturality (ar.hom.app M)
    have hd := kd.hom.naturality (ar.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn hk hd
    rw [← Category.assoc (gb.hom.app _), ← hn]
    simp only [Category.assoc]
    rw [hk]
    rw [hd]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ (F.J Y B T.cg.i).map ((F.P U Y T.cf.g).map (ta M)) ≫ k ≫
        (F.P V' B (r.rfg.hom ≫ T.p)).map (ar.hom.app M))
      (hv ((F.J X U' R.cf.i).obj M))
  let l := F.pComp V B Z T.p T.cg.g T.cfg.g T.p_g
  let m := F.pComp V' V Z r.rfg.hom T.cfg.g R.cfg.g r.rfg.hom_g
  let n := F.pComp B' B Z r.rg.hom T.cg.g R.cg.g r.rg.hom_g
  let o := F.pComp V' B' Z R.p R.cg.g R.cfg.g R.p_g
  let z := F.pComp V' B Z (r.rfg.hom ≫ T.p) T.cg.g R.cfg.g
    (by rw [Category.assoc, T.p_g, r.rfg.hom_g])
  rw [Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight,
    Functor.whiskerLeft_comp_whiskerRight]
  ext M
  dsimp only [towerIso, rho, H, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator, Functor.leftUnitor, Functor.comp_map, Functor.comp_obj]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  change
    (F.P B Z T.cg.g).map (gb.hom.app ((F.J X U T.cf.i).obj M)) ≫
      (F.P B Z T.cg.g).map ((F.P V B T.p).map (aT.hom.app M)) ≫
      l.hom.app ((F.J X V T.cfg.i).obj M) ≫
      (F.P V Z T.cfg.g).map ((F.J X V T.cfg.i).map ((F.pId X).inv.app M)) ≫
      (F.P V Z T.cfg.g).map (ge.hom.app M) ≫
      m.hom.app ((F.J X V' R.cfg.i).obj M) =
    (F.P B Z T.cg.g).map ((F.J Y B T.cg.i).map
      ((F.P U Y T.cf.g).map ((F.J X U T.cf.i).map ((F.pId X).inv.app M)))) ≫
      (F.P B Z T.cg.g).map ((F.J Y B T.cg.i).map
        ((F.P U Y T.cf.g).map (ga.hom.app M))) ≫
      (F.P B Z T.cg.g).map ((F.J Y B T.cg.i).map
        (pt.hom.app ((F.J X U' R.cf.i).obj M))) ≫
      (F.P B Z T.cg.g).map ((F.J Y B T.cg.i).map
        ((F.pId Y).inv.app ((F.P U' Y R.cf.g).obj ((F.J X U' R.cf.i).obj M)))) ≫
      (F.P B Z T.cg.g).map
        (gd.hom.app ((F.P U' Y R.cf.g).obj ((F.J X U' R.cf.i).obj M))) ≫
      n.hom.app ((F.J Y B' R.cg.i).obj
        ((F.P U' Y R.cf.g).obj ((F.J X U' R.cf.i).obj M))) ≫
      (F.P B' Z R.cg.g).map (gc.hom.app ((F.J X U' R.cf.i).obj M)) ≫
      (F.P B' Z R.cg.g).map ((F.P V' B' R.p).map (ar.hom.app M)) ≫
      o.hom.app ((F.J X V' R.cfg.i).obj M)
  have hn₁ := n.hom.naturality (gc.hom.app ((F.J X U' R.cf.i).obj M))
  have hn₂ := n.hom.naturality ((F.P V' B' R.p).map (ar.hom.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₁ hn₂
  rw [← Category.assoc (n.hom.app _), ← hn₁]
  simp only [Category.assoc]
  rw [← Category.assoc (n.hom.app _), ← hn₂]
  simp only [Category.assoc]
  rw [← F.pAssoc V' B' B Z R.p r.rg.hom T.cg.g (r.rfg.hom ≫ T.p) R.cg.g
    R.cfg.g r.p_comm.symm r.rg.hom_g
    (by rw [Category.assoc, T.p_g, r.rfg.hom_g]) R.p_g]
  rw [← Category.assoc ((F.P V Z T.cfg.g).map _), ← Functor.map_comp]
  change
    (F.P B Z T.cg.g).map (gb.hom.app ((F.J X U T.cf.i).obj M)) ≫
      (F.P B Z T.cg.g).map ((F.P V B T.p).map (aT.hom.app M)) ≫
      l.hom.app ((F.J X V T.cfg.i).obj M) ≫
      (F.P V Z T.cfg.g).map (te M) ≫ m.hom.app ((F.J X V' R.cfg.i).obj M) = _
  have hl := l.hom.naturality (te M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hl
  rw [← Category.assoc (l.hom.app _), ← hl]
  simp only [Category.assoc]
  rw [← F.pAssoc V' V B Z r.rfg.hom T.p T.cg.g (r.rfg.hom ≫ T.p) T.cfg.g
    R.cfg.g rfl T.p_g (by rw [Category.assoc, T.p_g, r.rfg.hom_g]) r.rfg.hom_g]
  simp only [← Category.assoc]
  apply (cancel_mono (z.hom.app ((F.J X V' R.cfg.i).obj M))).mpr
  simp only [← Functor.map_comp]
  congr 1
  simpa only [ta, td, Category.assoc, Functor.map_comp] using core M

end AlgebraicGeometry.ProperOpenCalculus
