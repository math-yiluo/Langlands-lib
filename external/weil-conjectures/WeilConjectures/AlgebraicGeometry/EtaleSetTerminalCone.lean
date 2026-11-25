/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalRestriction
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison

/-! # Compatibility of terminal section identifications

Source: Stacks Project, Tags 03S2, 03CB and 03CC.
(blueprint: lem-weil-pbc-sets-terminal-cone).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable abbrev setPullback {R S : Scheme.{u}} (f : S ⟶ R) :=
  Scheme.etaleSetPullback f

private noncomputable abbrev sitePullback {R S : Scheme.{u}} (f : S ⟶ R) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

private noncomputable abbrev inverseImageUnit (S T : Scheme.{u}) (e : T ⟶ S)
    [(sitePullback e).IsContinuous (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale)] :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (sitePullback e)
    (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- The composite unit, restricted along a diagonal, equals the two successive units.
private lemma terminal_unit_lift
    {R S T : Scheme.{u}} (e : S ⟶ R)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale)
    (t : T ⟶ U.left) (v : T ⟶ S) (hp : t ≫ U.hom = v ≫ e) :
    let d : Scheme.Etale.mk (𝟙 T) ⟶ (sitePullback (v ≫ e)).obj U :=
      MorphismProperty.Over.homMk (pullback.lift t (𝟙 T) hp) (pullback.lift_snd _ _ _)
    let D : Scheme.Etale.mk (𝟙 T) ⟶ (sitePullback v).obj ((sitePullback e).obj U) :=
      MorphismProperty.Over.homMk
        (pullback.lift (pullback.lift t v hp) (𝟙 T)
          (by exact (pullback.lift_snd t v hp).trans (Category.id_comp v).symm))
        (pullback.lift_snd _ _ _)
    ((inverseImageUnit R T (v ≫ e)).app H).hom.app (op U) ≫
        ((setPullback (v ≫ e)).obj H).obj.map d.op ≫
        inv (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          R S T e v).hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 T)))) =
      ((inverseImageUnit R S e).app H).hom.app (op U) ≫
        ((inverseImageUnit S T v).app ((setPullback e).obj H)).hom.app (op ((sitePullback
      e).obj U)) ≫
        ((setPullback v).obj ((setPullback e).obj H)).obj.map D.op := by
  dsimp only
  let D : Scheme.Etale.mk (𝟙 T) ⟶ (sitePullback v).obj ((sitePullback e).obj U) :=
    MorphismProperty.Over.homMk
      (pullback.lift (pullback.lift t v hp) (𝟙 T)
          (by exact (pullback.lift_snd t v hp).trans (Category.id_comp v).symm))
      (pullback.lift_snd _ _ _)
  let β := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T e v).hom.app H
  change ((inverseImageUnit R T (v ≫ e)).app H).hom.app (op U) ≫
      ((setPullback (v ≫ e)).obj H).obj.map _ ≫
      inv (β.hom.app (op (Scheme.Etale.mk (𝟙 T)))) =
    ((inverseImageUnit R S e).app H).hom.app (op U) ≫
      ((inverseImageUnit S T v).app ((setPullback e).obj H)).hom.app (op ((sitePullback e).obj U)) ≫
      ((setPullback v).obj ((setPullback e).obj H)).obj.map D.op
  apply (cancel_mono (β.hom.app (op (Scheme.Etale.mk (𝟙 T))))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  erw [β.hom.naturality D.op]
  have hu : ((inverseImageUnit R S e).app H).hom.app (op U) ≫
      ((inverseImageUnit S T v).app ((setPullback e).obj H)).hom.app (op ((sitePullback e).obj U)) ≫
      β.hom.app (op ((sitePullback v).obj ((sitePullback e).obj U))) =
    ((inverseImageUnit R T (v ≫ e)).app H).hom.app (op U) ≫
      ((setPullback (v ≫ e)).obj H).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) v e).inv.app U).op := by
    ext s
    exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
      R S T e v H U s
  erw [Category.assoc, reassoc_of% hu, ← Functor.map_comp, ← op_comp]
  apply congrArg (fun z ↦ ((inverseImageUnit R T (v ≫ e)).app H).hom.app (op U) ≫
    ((setPullback (v ≫ e)).obj H).obj.map z)
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift t (𝟙 T) hp =
    pullback.lift (pullback.lift t v hp) (𝟙 T) _ ≫
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) v e).inv.app U).left
  rw [MorphismProperty.Over.pullbackComp_inv_app_left]
  apply pullback.hom_ext <;> simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
-- Restriction-unit compatibility with any identification of the localized identity object.
private lemma terminalRestriction_unit
    {R : Scheme.{u}} (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (U V : R.Etale) (f : V ⟶ U)
    (e : (MorphismProperty.Over.map (P := @Etale) ⊤ V.prop).obj
      (Scheme.Etale.mk (𝟙 V.left)) ≅ V) :
    let : (MorphismProperty.Over.pullback @Etale ⊤ V.hom).IsContinuous
      (R.smallGrothendieckTopology @Etale) (V.left.smallGrothendieckTopology @Etale) :=
      Etale.isContinuous_overPullback V.hom
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ V.hom) (Type (u + 1))
      (R.smallGrothendieckTopology @Etale)
      (V.left.smallGrothendieckTopology @Etale)).unit.app H).hom.app (op U)) ≫
        ((Scheme.etaleSetPullback V.hom).obj H).obj.map
          (MorphismProperty.Over.homMk
            (B := (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj U)
            (pullback.lift (e.hom.left ≫ f.left) (𝟙 _) (by
              rw [Category.assoc, MorphismProperty.Over.w f, MorphismProperty.Over.w e.hom]
              exact Category.id_comp _))
            (pullback.lift_snd _ _ _)).op =
      H.obj.map f.op ≫ H.obj.map e.hom.op ≫
        inv (((Classical.choose (etaleSetInverseImageRestriction V.hom)).hom.app H).hom.app
          (op (Scheme.Etale.mk (𝟙 V.left)))) := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ V.hom).IsContinuous
      (R.smallGrothendieckTopology @Etale) (V.left.smallGrothendieckTopology @Etale) :=
      Etale.isContinuous_overPullback V.hom
  let ρ := Classical.choose (etaleSetInverseImageRestriction V.hom)
  let d : Scheme.Etale.mk (𝟙 V.left) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj U :=
    MorphismProperty.Over.homMk
      (pullback.lift (e.hom.left ≫ f.left) (𝟙 _) (by
        rw [Category.assoc, MorphismProperty.Over.w f, MorphismProperty.Over.w e.hom]
        exact Category.id_comp _))
      (pullback.lift_snd _ _ _)
  let F := (Scheme.etaleSetPullback V.hom).obj H
  let K := (Etale.localizationRestriction (Type (u + 1)) V.hom inferInstance).obj H
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ V.hom) (Type (u + 1))
    (R.smallGrothendieckTopology @Etale)
    (V.left.smallGrothendieckTopology @Etale)).unit.app H).hom.app (op U)
  change η ≫ F.obj.map d.op = H.obj.map f.op ≫
    H.obj.map e.hom.op ≫ inv ((ρ.hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 V.left))))
  apply (cancel_mono ((ρ.hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 V.left))))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  calc
    η ≫ F.obj.map d.op ≫ (ρ.hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 V.left))) =
        η ≫ (ρ.hom.app H).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj U)) ≫
          K.obj.map d.op := by rw [(ρ.hom.app H).hom.naturality d.op]
    _ = H.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ V.hom
          inferInstance trivial).counit.app U).op ≫ K.obj.map d.op := by
        rw [← Category.assoc]
        congr 1
        ext s
        exact Classical.choose_spec (etaleSetInverseImageRestriction V.hom) H U s
    _ = H.obj.map f.op ≫ H.obj.map e.hom.op := by
        change H.obj.map _ ≫ H.obj.map _ = _
        rw [← H.obj.map_comp, ← H.obj.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        simp only [unop_comp, Quiver.Hom.unop_op, Functor.op_map]
        apply MorphismProperty.Over.Hom.ext
        simp [d, MorphismProperty.Over.mapPullbackAdj]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- Specialize the composite-unit calculation to the structure map of an étale object.
private lemma terminal_diagonal_unit
    {R T : Scheme.{u}} (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (U : R.Etale) (t : T ⟶ U.left) :
    let : (sitePullback (t ≫ U.hom)).IsContinuous
      (R.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale) :=
      Etale.isContinuous_overPullback (t ≫ U.hom)
    ((inverseImageUnit R T (t ≫ U.hom)).app H).hom.app (op U) ≫
        ((setPullback (t ≫ U.hom)).obj H).obj.map
          (MorphismProperty.Over.homMk (B := (sitePullback (t ≫ U.hom)).obj U)
            (pullback.lift t (𝟙 T) rfl) (pullback.lift_snd _ _ _)).op =
      (etaleSetTerminalRestriction H U).hom ≫
        ((inverseImageUnit U.left T t).app ((setPullback U.hom).obj H)).hom.app
          (op (Scheme.Etale.mk (𝟙 U.left))) ≫
        ((setPullback t).obj ((setPullback U.hom).obj H)).obj.map
          (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 U.left) t))
            (Category.comp_id _)).inv.op ≫
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          R U.left T U.hom t).hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 T)))) := by
  let : (sitePullback (t ≫ U.hom)).IsContinuous
      (R.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale) :=
      Etale.isContinuous_overPullback (t ≫ U.hom)
  let : (sitePullback U.hom).IsContinuous
      (R.smallGrothendieckTopology @Etale) (U.left.smallGrothendieckTopology @Etale) :=
    Etale.isContinuous_overPullback U.hom
  let : (sitePullback t).IsContinuous
      (U.left.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale) :=
    Etale.isContinuous_overPullback t
  let d : Scheme.Etale.mk (𝟙 U.left) ⟶ (sitePullback U.hom).obj U :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp))
      (pullback.lift_snd _ _ _)
  let a : (sitePullback t).obj (Scheme.Etale.mk (𝟙 U.left)) ≅ Scheme.Etale.mk (𝟙 T) :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 U.left) t)) (Category.comp_id _)
  let β := (Classical.choose etaleSetInverseImageCompositionUnits.2.2
    R U.left T U.hom t).hom.app H
  have hr' : ((inverseImageUnit R U.left U.hom).app H).hom.app (op U) ≫
      ((setPullback U.hom).obj H).obj.map d.op = (etaleSetTerminalRestriction H U).hom := by
    let e : (MorphismProperty.Over.map (P := @Etale) ⊤ U.prop).obj
        (Scheme.Etale.mk (𝟙 U.left)) ≅ U :=
      MorphismProperty.Over.isoMk (Iso.refl U.left) (by simp)
    have hr := terminalRestriction_unit H U U (𝟙 U) e
    have he : e.hom.left = 𝟙 U.left := rfl
    have hf : (𝟙 U : U ⟶ U).left = 𝟙 U.left := rfl
    dsimp only at hr
    simp only [he, hf] at hr
    change _ = H.obj.map (𝟙 U).op ≫ (etaleSetTerminalRestriction H U).hom at hr
    exact hr.trans (by rw [op_id, CategoryTheory.Functor.map_id, Category.id_comp])
  have hn := ((inverseImageUnit U.left T t).app ((setPullback U.hom).obj H)).hom.naturality d.op
  have hu := terminal_unit_lift U.hom H U t t rfl
  dsimp only at hu
  change ((inverseImageUnit R T (t ≫ U.hom)).app H).hom.app (op U) ≫
    ((setPullback (t ≫ U.hom)).obj H).obj.map _ =
    (etaleSetTerminalRestriction H U).hom ≫
      ((inverseImageUnit U.left T t).app ((setPullback U.hom).obj H)).hom.app
        (op (Scheme.Etale.mk (𝟙 U.left))) ≫
      ((setPullback t).obj ((setPullback U.hom).obj H)).obj.map a.inv.op ≫
      β.hom.app (op (Scheme.Etale.mk (𝟙 T)))
  rw [← hr']
  change ((inverseImageUnit R T (t ≫ U.hom)).app H).hom.app (op U) ≫
      ((setPullback (t ≫ U.hom)).obj H).obj.map _ =
    ((inverseImageUnit R U.left U.hom).app H).hom.app (op U) ≫
      ((setPullback U.hom).obj H).obj.map d.op ≫
      ((inverseImageUnit U.left T t).app ((setPullback U.hom).obj H)).hom.app
        (op (Scheme.Etale.mk (𝟙 U.left))) ≫
      ((setPullback t).obj ((setPullback U.hom).obj H)).obj.map a.inv.op ≫
      β.hom.app (op (Scheme.Etale.mk (𝟙 T)))
  change ((setPullback U.hom).obj H).obj.map d.op ≫
      ((inverseImageUnit U.left T t).app ((setPullback U.hom).obj H)).hom.app
        (op (Scheme.Etale.mk (𝟙 U.left))) =
    ((inverseImageUnit U.left T t).app ((setPullback U.hom).obj H)).hom.app (op
      ((sitePullback U.hom).obj U)) ≫
      ((setPullback t).obj ((setPullback U.hom).obj H)).obj.map ((sitePullback t).map d).op at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, ← op_comp]
  have hd : a.inv ≫ (sitePullback t).map d =
      MorphismProperty.Over.homMk
        (pullback.lift (pullback.lift t t rfl) (𝟙 T)
          (by exact (pullback.lift_snd t t rfl).trans (Category.id_comp t).symm))
        (pullback.lift_snd _ _ _) := by
    apply MorphismProperty.Over.Hom.ext
    change a.inv.left ≫ ((sitePullback t).map d).left = _
    dsimp [a, MorphismProperty.Over.pullback]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      apply pullback.hom_ext <;> simp [d, Category.assoc]
    · simp
  rw [hd]
  apply (cancel_mono (inv (β.hom.app (op (Scheme.Etale.mk (𝟙 T)))))).1
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact hu

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- Compatibility of terminal transport with a section comparison: unit naturality,
-- associativity of composition, and equality of the canonical pullback maps.
private lemma terminal_transport_comparison
    {R S V T : Scheme.{u}} (e : S ⟶ R) (f : V ⟶ S) (h : T ⟶ V)
    (k : V ⟶ R) (l : T ⟶ S) (p : T ⟶ R)
    (hk : f ≫ e = k) (hl : h ≫ f = l) (hp : h ≫ k = p) (hp₀ : l ≫ e = p)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    ((inverseImageUnit V T h).app ((setPullback k).obj H)).hom.app (op (Scheme.Etale.mk (𝟙 V))) ≫
        (etaleSetTerminalTransport k h p hp H).inv ≫
        (etaleSetTerminalTransport e l p hp₀ H).hom =
      (etaleSetTerminalTransport e f k hk H).hom ≫
        etaleSetSectionComparison h f l hl ((setPullback e).obj H) (Scheme.Etale.mk (𝟙 S)) := by
  subst k
  subst l
  subst p
  let A := Scheme.Etale.mk (𝟙 S)
  let B := Scheme.Etale.mk (𝟙 V)
  let C := Scheme.Etale.mk (𝟙 T)
  let a : (sitePullback f).obj A ≅ B :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) f)) (Category.comp_id _)
  let d : (sitePullback h).obj B ≅ C :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 V) h)) (Category.comp_id _)
  let z : (sitePullback (h ≫ f)).obj A ≅ C :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) (h ≫ f))) (Category.comp_id _)
  let α := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S V e f).hom.app H
  let β := (Classical.choose etaleSetInverseImageCompositionUnits.2.2
    R V T (f ≫ e) h).hom.app H
  let γ := (Classical.choose etaleSetInverseImageCompositionUnits.2.2
    R S T e (h ≫ f)).hom.app H
  let δ := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 S V T f h).hom.app
    ((setPullback e).obj H)
  have hs := NatTrans.congr_app (congrArg (fun v ↦ v.hom)
    ((inverseImageUnit V T h).naturality α)) (op B)
  have hc := NatTrans.congr_app (congrArg (fun v ↦ v.hom)
    ((Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.2
      R S V T e f h H)) (op C)
  have hn := ((inverseImageUnit V T h).app ((setPullback f).obj ((setPullback e).obj
      H))).hom.naturality a.hom.op
  simp only [etaleSetTerminalTransport, etaleSetSectionComparison, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, eqToIso_refl, Iso.refl_hom,
    Iso.refl_inv, eqToHom_refl, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
  change ((inverseImageUnit V T h).app ((setPullback (f ≫ e)).obj H)).hom.app (op B) ≫
      ((setPullback h).obj ((setPullback (f ≫ e)).obj H)).obj.map d.inv.op ≫
      β.hom.app (op C) ≫ inv (γ.hom.app (op C)) ≫
      ((setPullback (h ≫ f)).obj ((setPullback e).obj H)).obj.map z.hom.op =
    inv (α.hom.app (op B)) ≫ ((setPullback f).obj ((setPullback e).obj H)).obj.map a.hom.op ≫
      ((inverseImageUnit V T h).app ((setPullback f).obj ((setPullback e).obj H))).hom.app
      (op ((sitePullback f).obj A)) ≫
      δ.hom.app (op ((sitePullback h).obj ((sitePullback f).obj A))) ≫
      ((setPullback (h ≫ f)).obj ((setPullback e).obj H)).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom.app A).op
  change α.hom.app (op B) ≫ ((inverseImageUnit V T h).app ((setPullback (f
      ≫ e)).obj H)).hom.app (op B) =
    ((inverseImageUnit V T h).app ((setPullback f).obj ((setPullback e).obj H))).hom.app (op B) ≫
      ((setPullback h).map α).hom.app (op ((sitePullback h).obj B)) at hs
  change ((setPullback h).map α).hom.app (op C) ≫ β.hom.app (op C) =
    δ.hom.app (op C) ≫ γ.hom.app (op C) at hc
  change ((setPullback f).obj ((setPullback e).obj H)).obj.map a.hom.op ≫
      ((inverseImageUnit V T h).app ((setPullback f).obj ((setPullback e).obj H))).hom.app
      (op ((sitePullback f).obj A)) =
    ((inverseImageUnit V T h).app ((setPullback f).obj ((setPullback e).obj H))).hom.app (op B) ≫
      ((setPullback h).obj ((setPullback f).obj ((setPullback e).obj H))).obj.map
      ((sitePullback h).map a.hom).op at hn
  apply (cancel_epi (α.hom.app (op B))).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [reassoc_of% hs]
  have hα := ((setPullback h).map α).hom.naturality d.inv.op
  rw [← reassoc_of% hα, reassoc_of% hc]
  simp only [IsIso.hom_inv_id_assoc]
  rw [reassoc_of% hn]
  have hδ := δ.hom.naturality ((sitePullback h).map a.hom).op
  have hδ' := δ.hom.naturality d.inv.op
  rw [reassoc_of% hδ, reassoc_of% hδ']
  simp only [← Functor.map_comp, ← op_comp]
  have hp : z.hom ≫ d.inv =
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom.app A ≫
        (sitePullback h).map a.hom := by
    apply MorphismProperty.Over.Hom.ext
    change z.hom.left ≫ d.inv.left =
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom.app A).left ≫
        ((sitePullback h).map a.hom).left
    dsimp only [z, d, a]
    rw [MorphismProperty.Over.pullbackComp_hom_app_left]
    apply pullback.hom_ext <;> simp [A, B, MorphismProperty.Over.pullback, Category.assoc]
  rw [hp]


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Tag 03S2 and Sites Tags 03CB and 03CC;
the canonical comparison calculation in the degree-zero route of Tag 09YQ.
(blueprint: lem-weil-pbc-sets-terminal-cone).

Proof: Expand terminal transport and section comparison. The composition-unit
equation for the structure morphism of `W` and the map to `W` identifies the
iterated pulled-back section with the section pulled back along `p`. The
restriction-unit equation at the étale object `U` identifies the input section
with its restriction to the terminal object over `U`. Naturality of both units
moves this section through the comparison. Associativity of inverse-image
composition makes the two composition isomorphisms agree. After cancelling
these isomorphisms, the two maps of pullbacks have first projection `t` and
second projection the identity, so pullback uniqueness identifies both with the
explicit diagonal lift below. Equality transports depend only on their endpoints.
No étaleness assumption is used on `p`, `t` or `t₀`; thus identity maps, empty
schemes and arbitrary cone legs are included. -/
theorem etaleSetTerminalCone
    {R T : Scheme.{u}} (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (U W : R.Etale) (q : U ⟶ W) (p : T ⟶ R) (t : T ⟶ U.left) (t₀ : T ⟶ W.left)
    (ht : t ≫ q.left = t₀) (hp : t ≫ U.hom = p) (hp₀ : t₀ ≫ W.hom = p) :
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
      (R.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale)).unit.app H).hom.app (op U)) ≫
        ((Scheme.etaleSetPullback p).obj H).obj.map
          (MorphismProperty.Over.homMk
            (B := (MorphismProperty.Over.pullback @Etale ⊤ p).obj U)
            (pullback.lift t (𝟙 _) (by simpa using hp))
            (pullback.lift_snd _ _ _)).op ≫
        (etaleSetTerminalTransport W.hom t₀ p hp₀ H).hom =
      (etaleSetTerminalRestriction H U ≪≫
        etaleSetTerminalTransport W.hom q.left U.hom (MorphismProperty.Over.w q) H).hom ≫
      etaleSetSectionComparison t q.left t₀ ht
        ((Scheme.etaleSetPullback W.hom).obj H) (Scheme.Etale.mk (𝟙 W.left)) := by
  subst p
  let : (sitePullback (t ≫ U.hom)).IsContinuous
      (R.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale) :=
    Etale.isContinuous_overPullback (t ≫ U.hom)
  have hd := terminal_diagonal_unit H U t
  have hc := terminal_transport_comparison W.hom q.left t U.hom t₀ (t ≫ U.hom)
    (MorphismProperty.Over.w q) ht rfl hp₀ H
  change ((inverseImageUnit R T (t ≫ U.hom)).app H).hom.app (op U) ≫
      ((setPullback (t ≫ U.hom)).obj H).obj.map _ ≫
      (etaleSetTerminalTransport W.hom t₀ (t ≫ U.hom) hp₀ H).hom = _
  have hd' : ((inverseImageUnit R T (t ≫ U.hom)).app H).hom.app (op U) ≫
      ((setPullback (t ≫ U.hom)).obj H).obj.map
        (MorphismProperty.Over.homMk (B := (sitePullback (t ≫ U.hom)).obj U)
          (pullback.lift t (𝟙 T) rfl) (pullback.lift_snd _ _ _)).op =
    (etaleSetTerminalRestriction H U).hom ≫
      ((inverseImageUnit U.left T t).app ((setPullback U.hom).obj H)).hom.app
        (op (Scheme.Etale.mk (𝟙 U.left))) ≫
      (etaleSetTerminalTransport U.hom t (t ≫ U.hom) rfl H).inv := by
    simp only [etaleSetTerminalTransport, Iso.trans_inv, Iso.symm_inv,
      eqToIso_refl, Iso.refl_hom, asIso_hom, Category.comp_id,
      Functor.mapIso_inv, Iso.op_inv]
    convert hd using 1; rfl
  erw [← Category.assoc, hd']
  simp only [Iso.trans_hom, Category.assoc]
  convert congrArg (fun v ↦ (etaleSetTerminalRestriction H U).hom ≫ v) hc using 1 <;> rfl

end AlgebraicGeometry
