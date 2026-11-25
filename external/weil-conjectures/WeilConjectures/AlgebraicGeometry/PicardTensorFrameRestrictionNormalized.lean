/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PicardTensorFrameCoordinates
public import WeilConjectures.AlgebraicGeometry.PicardOrdinaryModelCycles
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections
@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
universe v
namespace Modules
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 2048 in
private lemma unit_comp {X Y Z : Scheme.{v}} (i : X ⟶ Y) (g : Y ⟶ Z)
    (g' : X ⟶ Z) (h : i ≫ g = g') :
    ((conjugateIsoEquiv
      ((Classical.choose (exists_tensorPullbackAdjunction g)).comp
        (Classical.choose (exists_tensorPullbackAdjunction i)))
      (Classical.choose (exists_tensorPullbackAdjunction g'))).symm
        (pushforwardComp i g ≪≫ pushforwardCongr h)).hom.app (Modules.unit Z) ≫
      (tensorPullback i).map (picardTensorFrameUnitIso g).hom ≫
        (picardTensorFrameUnitIso i).hom = (picardTensorFrameUnitIso g').hom := by
  let ag := Classical.choose (exists_tensorPullbackAdjunction g)
  let ai := Classical.choose (exists_tensorPullbackAdjunction i)
  let ag' := Classical.choose (exists_tensorPullbackAdjunction g')
  let b := pushforwardComp i g ≪≫ pushforwardCongr h
  let A := (conjugateIsoEquiv (ag.comp ai) ag').symm b
  let u := (tensorPullback i).map (picardTensorFrameUnitIso g).hom ≫
    (picardTensorFrameUnitIso i).hom
  change A.hom.app _ ≫ u = _
  apply (ag'.homEquiv _ _).injective
  have ht : ag'.homEquiv _ _ (A.hom.app _ ≫ u) =
      (ag.comp ai).homEquiv _ _ u ≫ b.hom.app _ := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    change (ag'.unit.app _ ≫ (pushforward g').map
      (((conjugateEquiv (ag.comp ai) ag').symm b.hom).app _)) ≫ _ = _
    rw [← unit_conjugateEquiv_symm, Category.assoc, ← b.hom.naturality,
      ← Category.assoc]
    rw [Adjunction.homEquiv_unit]
  rw [ht]
  have hg : ag.homEquiv _ _ (picardTensorFrameUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    (ag.homEquiv _ _).apply_symm_apply _
  have hi : ai.homEquiv _ _ (picardTensorFrameUnitIso i).hom =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom :=
    (ai.homEquiv _ _).apply_symm_apply _
  have hg' : ag'.homEquiv _ _ (picardTensorFrameUnitIso g').hom =
      SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom :=
    (ag'.homEquiv _ _).apply_symm_apply _
  rw [hg']
  dsimp only [u]
  rw [Adjunction.comp_homEquiv]
  change ag.homEquiv _ _ (ai.homEquiv _ _
    ((tensorPullback i).map (picardTensorFrameUnitIso g).hom ≫
      (picardTensorFrameUnitIso i).hom)) ≫ b.hom.app _ = _
  rw [Adjunction.homEquiv_naturality_left, hi,
    Adjunction.homEquiv_naturality_right, hg]
  subst g'
  ext U a
  have he : i.app (g ⁻¹ᵁ U) (g.app U a) = (i ≫ g).app U a :=
    (ConcreteCategory.congr_hom (Scheme.Hom.comp_app i g U) a).symm
  simp only [pushforward_obj_obj, Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
    Iso.trans_hom, NatTrans.comp_app, Functor.comp_obj, Category.assoc, Hom.comp_app,
    pushforward_map_app, pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, b]
  exact he

private lemma tensorUnit_conj_app_top {X Y : Scheme.{v}} (g : X ⟶ Y)
    (f : Modules.unit Y ⟶ Modules.unit Y) :
    Hom.app ((picardTensorFrameUnitIso g).inv ≫ (tensorPullback g).map f ≫
        (picardTensorFrameUnitIso g).hom) ⊤ (1 : Γ(X, ⊤)) =
      g.appTop (Hom.app f ⊤ (1 : Γ(Y, ⊤))) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  set F := (picardTensorFrameUnitIso g).inv ≫ (tensorPullback g).map f ≫
    (picardTensorFrameUnitIso g).hom
  have hF : (tensorPullback g).map f ≫ (picardTensorFrameUnitIso g).hom =
      (picardTensorFrameUnitIso g).hom ≫ F := by simp [F]
  have key := congrArg (adj.homEquiv _ _) hF
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at key
  have h2 : adj.homEquiv _ _ (picardTensorFrameUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    (adj.homEquiv _ _).apply_symm_apply _
  rw [h2] at key
  have he := congrArg (fun (φ : Modules.unit Y ⟶ (pushforward g).obj (Modules.unit X)) ↦
    Hom.app φ ⊤ (1 : Γ(Y, ⊤))) key
  dsimp only at he
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at he
  have e1 : Hom.app (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ⊤
      (1 : Γ(Y, ⊤)) = (1 : Γ(X, ⊤)) := map_one g.appTop.hom
  exact (he.trans (congrArg (Hom.app F (g ⁻¹ᵁ ⊤)) e1)).symm

end Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 2048 in
/-- Normalized restriction applies the global-section ring map.
Source: Stacks Project, Tag 0096.
(blueprint: lem-sc-picard-tensor-frame-restriction-normalized)
Proof: Apply the direct adjunction to the composition comparison on the unit.
Its adjunct is the composite structure map by the mate unit equation. This
proves compatibility of the comparison with the two pinned unit isomorphisms.
Naturality with respect to q cancels the target frame. The source unit
compatibility cancels the source frame. The remaining morphism is the unit
conjugate of the pullback of the normalized endomorphism. Evaluate at one;
adjunction naturality gives the ring map applied to its original value. -/
theorem picardTensorFrame_restriction_normalized (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU :
    w ∈ U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (q :
    (Modules.overEquiv U).functor.obj (K.X 0) ≅ Modules.unit U.toScheme) (V : W.Opens) (hwV : w
    ∈ V) (hVU : V ≤ U) (hs : picardResidueLift W w V hwV ≫ W.homOfLE hVU = picardResidueLift W
    w U hwU) (f : (Modules.tensorPullback V.ι).obj (Modules.unit W) ⟶ (Modules.tensorPullback
    (W.homOfLE hVU)).obj ((Modules.overEquiv U).functor.obj (K.X 0))) :
    Modules.picardTensorScalarCoordinate (W.fromSpecResidueField w) (picardResidueLift W w U
    hwU) q (picardOrdinaryModelRestriction W U K (picardResidueLift W w V hwV) V.ι
    (W.fromSpecResidueField w) (W.homOfLE hVU) (picardResidueLift W w U hwU)
    (picardResidueLift_comp W w V hwV) hs f) = (picardResidueLift W w V hwV).appTop
    (Modules.picardTensorScalarCoordinate V.ι (W.homOfLE hVU) q f)  := by
  let i := picardResidueLift W w V hwV
  let t := V.ι
  let t' := W.fromSpecResidueField w
  let s := W.homOfLE hVU
  let s' := picardResidueLift W w U hwU
  let At := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction t)).comp
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction t'))).symm
      (Modules.pushforwardComp i t ≪≫
        Modules.pushforwardCongr (picardResidueLift_comp W w V hwV))
  let As := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction s)).comp
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction s'))).symm
      (Modules.pushforwardComp i s ≪≫ Modules.pushforwardCongr hs)
  have ht0 : At.hom.app (Modules.unit W) ≫
      (Modules.tensorPullback i).map (Modules.picardTensorFrameUnitIso t).hom ≫
        (Modules.picardTensorFrameUnitIso i).hom =
      (Modules.picardTensorFrameUnitIso t').hom :=
    Modules.unit_comp i t t' (picardResidueLift_comp W w V hwV)
  have hs0 : As.hom.app (Modules.unit U.toScheme) ≫
      (Modules.tensorPullback i).map (Modules.picardTensorFrameUnitIso s).hom ≫
        (Modules.picardTensorFrameUnitIso i).hom =
      (Modules.picardTensorFrameUnitIso s').hom :=
    Modules.unit_comp i s s' hs
  have ht1 : (Modules.picardTensorFrameUnitIso t').inv ≫ At.hom.app (Modules.unit W) =
      (Modules.picardTensorFrameUnitIso i).inv ≫
        (Modules.tensorPullback i).map (Modules.picardTensorFrameUnitIso t).inv := by
    apply (cancel_mono ((Modules.tensorPullback i).map
      (Modules.picardTensorFrameUnitIso t).hom ≫ (Modules.picardTensorFrameUnitIso i).hom)).mp
    simp only [Category.assoc]
    rw [ht0]
    have hc := ((Modules.tensorPullback i).mapIso
      (Modules.picardTensorFrameUnitIso t)).inv_hom_id
    dsimp only [Functor.mapIso_hom, Functor.mapIso_inv] at hc
    rw [reassoc_of% hc, Iso.inv_hom_id]
    simp only [Iso.inv_hom_id]
  have hs1 : As.inv.app ((Modules.overEquiv U).functor.obj (K.X 0)) ≫
      (Modules.tensorPullback s').map q.hom ≫ (Modules.picardTensorFrameUnitIso s').hom =
      (Modules.tensorPullback i).map ((Modules.tensorPullback s).map q.hom) ≫
        (Modules.tensorPullback i).map (Modules.picardTensorFrameUnitIso s).hom ≫
          (Modules.picardTensorFrameUnitIso i).hom := by
    apply (cancel_epi (As.hom.app _)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    have hnat := As.hom.naturality q.hom
    dsimp only [Functor.comp_map] at hnat
    rw [← reassoc_of% hnat]
    change _ = (Modules.tensorPullback s').map q.hom ≫
      (As.hom.app _ ≫ (Modules.tensorPullback i).map
        (Modules.picardTensorFrameUnitIso s).hom ≫ (Modules.picardTensorFrameUnitIso i).hom)
    rw [hs0]
  let n := (Modules.picardTensorFrameUnitIso t).inv ≫ f ≫
    (Modules.tensorPullback s).map q.hom ≫ (Modules.picardTensorFrameUnitIso s).hom
  have hn : (Modules.picardTensorFrameUnitIso t').inv ≫
      (At.hom.app _ ≫ (Modules.tensorPullback i).map f ≫ As.inv.app _) ≫
        (Modules.tensorPullback s').map q.hom ≫ (Modules.picardTensorFrameUnitIso s').hom =
      (Modules.picardTensorFrameUnitIso i).inv ≫ (Modules.tensorPullback i).map n ≫
        (Modules.picardTensorFrameUnitIso i).hom := by
    simp only [Category.assoc]
    rw [hs1, ← Category.assoc, ht1]
    simp only [n, Functor.map_comp, Category.assoc]
  change Modules.Hom.app
    ((Modules.picardTensorFrameUnitIso t').inv ≫
      (At.hom.app _ ≫ (Modules.tensorPullback i).map f ≫ As.inv.app _) ≫
        (Modules.tensorPullback s').map q.hom ≫ (Modules.picardTensorFrameUnitIso s').hom)
    ⊤ (1 : Γ(Spec (W.residueField w), ⊤)) =
      i.appTop (Modules.Hom.app n ⊤ (1 : Γ(V.toScheme, ⊤)))
  rw [hn]
  exact Modules.tensorUnit_conj_app_top i n
end AlgebraicGeometry.Scheme
