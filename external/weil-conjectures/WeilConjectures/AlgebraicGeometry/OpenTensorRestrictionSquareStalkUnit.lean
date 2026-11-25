/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictionStalkSquare

/-! # Open restriction of the tensor-pullback adjunction unit

Source: Stacks Project, Tags 0096 and 0098.
(blueprint: lem-pc-open-tensor-restriction-square-stalk-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem open_iso_eq {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    openTensorRestrictionIso j =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
        (Scheme.Modules.restrictAdjunction j) := by
  apply Iso.ext
  simp only [openTensorRestrictionIso, Scheme.Modules.restrictFunctorIsoPullback,
    Iso.trans_hom, Iso.symm_hom]
  ext M
  simp only [NatTrans.comp_app]
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.leftAdjointUniq_trans_app]

private theorem open_unit {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (M : Z.Modules) :
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app M ≫
      (Scheme.Modules.pushforward j).map ((openTensorRestrictionIso j).hom.app M) =
        (Scheme.Modules.restrictAdjunction j).unit.app M := by
  rw [open_iso_eq]
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ _

private theorem composition_unit {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (h : Y ⟶ X) (k : Z ⟶ X) (w : g ≫ h = k)
    (M : X.Modules) :
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction h)).unit.app M ≫
      (Scheme.Modules.pushforward h).map
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
          ((Scheme.Modules.tensorPullback h).obj M)) ≫
      (Scheme.Modules.pushforwardComp g h ≪≫ Scheme.Modules.pushforwardCongr w).hom.app
        ((Scheme.Modules.tensorPullback g).obj ((Scheme.Modules.tensorPullback h).obj M)) =
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M ≫
      (Scheme.Modules.pushforward k).map
        ((Scheme.Modules.tensorPullbackCompositionIso g h k w).hom.app M) := by
  have t := unit_conjugateEquiv_symm
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction h)).comp
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k))
    (Scheme.Modules.pushforwardComp g h ≪≫ Scheme.Modules.pushforwardCongr w).hom M
  simpa only [Functor.comp_obj, Adjunction.comp_unit_app, Category.assoc,
    Scheme.Modules.tensorPullbackCompositionIso, conjugateIsoEquiv_symm_apply_hom] using t

-- Carry out the unit calculation with abstract functors. This keeps rewriting and
-- kernel conversion independent of the concrete tensor-pullback constructions.
private theorem unit_square_of_composition
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {K : C ⥤ D} {P R : D ⥤ F} {J S : C ⥤ E} {Q : E ⥤ F} {A : C ⥤ F}
    {Hk : D ⥤ C} {Hp : F ⥤ D} {Hj : E ⥤ C} {Hq : F ⥤ E} {Ha : F ⥤ C}
    (ak : K ⊣ Hk) (ap : P ⊣ Hp) (aj : J ⊣ Hj) (aq : Q ⊣ Hq) (aa : A ⊣ Ha)
    (ar : R ⊣ Hp) (as : S ⊣ Hj)
    (θp : P ≅ R) (θj : J ≅ S) (βp : A ≅ K ⋙ P) (βq : A ≅ J ⋙ Q)
    (cP : Hp ⋙ Hk ≅ Ha) (cQ : Hq ⋙ Hj ≅ Ha) (θ : K ⋙ R ≅ S ⋙ Q) (M : C)
    (hup : ap.unit.app (K.obj M) ≫ Hp.map (θp.hom.app (K.obj M)) =
      ar.unit.app (K.obj M))
    (huj : aj.unit.app M ≫ Hj.map (θj.hom.app M) = as.unit.app M)
    (hcP : ak.unit.app M ≫ Hk.map (ap.unit.app (K.obj M)) ≫
        cP.hom.app (P.obj (K.obj M)) = aa.unit.app M ≫ Ha.map (βp.hom.app M))
    (hcQ : aj.unit.app M ≫ Hj.map (aq.unit.app (J.obj M)) ≫
        cQ.hom.app (Q.obj (J.obj M)) = aa.unit.app M ≫ Ha.map (βq.hom.app M))
    (hθ : θp.hom.app (K.obj M) ≫ θ.hom.app M =
      βp.inv.app M ≫ βq.hom.app M ≫ Q.map (θj.hom.app M)) :
    ak.unit.app M ≫ Hk.map (ar.unit.app (K.obj M)) ≫
        (Hp ⋙ Hk).map (θ.hom.app M) =
      as.unit.app M ≫ Hj.map (aq.unit.app (S.obj M)) ≫
        cQ.hom.app (Q.obj (S.obj M)) ≫ cP.inv.app (Q.obj (S.obj M)) := by
  rw [← hup, ← huj]
  apply (cancel_mono (cP.hom.app (Q.obj (S.obj M)))).1
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change ak.unit.app M ≫ Hk.map (ap.unit.app (K.obj M)) ≫
      (Hp ⋙ Hk).map (θp.hom.app (K.obj M)) ≫
      (Hp ⋙ Hk).map (θ.hom.app M) ≫ cP.hom.app _ =
    aj.unit.app M ≫ Hj.map (θj.hom.app M) ≫ Hj.map (aq.unit.app (S.obj M)) ≫
      cQ.hom.app _
  rw [← Functor.map_comp_assoc, hθ, cP.hom.naturality]
  rw [reassoc_of% hcP]
  simp only [← Functor.map_comp, βp.hom_inv_id_app_assoc]
  have hn : Hj.map (θj.hom.app M) ≫ Hj.map (aq.unit.app (S.obj M)) =
      Hj.map (aq.unit.app (J.obj M)) ≫ (Hq ⋙ Hj).map (Q.map (θj.hom.app M)) := by
    rw [← Functor.map_comp, ← aq.unit_naturality, Functor.map_comp]
    rfl
  rw [reassoc_of% hn]
  conv_rhs =>
    rhs
    rhs
    erw [cQ.hom.naturality (Q.map (θj.hom.app M))]
  have hQ := congrArg (fun v ↦ v ≫ Ha.map (Q.map (θj.hom.app M))) hcQ
  simpa only [Category.assoc, Functor.map_comp] using hQ.symm

section
attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.pushforward
  Scheme.Modules.pushforwardComp Scheme.Modules.pushforwardCongr
  openTensorRestrictionIso openTensorRestrictionSquareIso

-- Elaborate the two composition mates with their specified adjunction units.
private theorem square_unit {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (M : X.Modules) :
    let p := pullback.fst k U.ι
    let q := pullback.snd k U.ι
    let cP := Scheme.Modules.pushforwardComp p k ≪≫ Scheme.Modules.pushforwardCongr rfl
    let cQ := Scheme.Modules.pushforwardComp q U.ι ≪≫
      Scheme.Modules.pushforwardCongr pullback.condition.symm
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M ≫
      (Scheme.Modules.pushforward k).map
        ((Scheme.Modules.restrictAdjunction p).unit.app
          ((Scheme.Modules.tensorPullback k).obj M)) ≫
      (Scheme.Modules.pushforward p ⋙ Scheme.Modules.pushforward k).map
        ((openTensorRestrictionSquareIso k U).hom.app M) =
    (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)).unit.app
          ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≫
      cQ.hom.app ((Scheme.Modules.tensorPullback q).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≫
      cP.inv.app ((Scheme.Modules.tensorPullback q).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) := by
  dsimp only
  let p := pullback.fst k U.ι
  let q := pullback.snd k U.ι
  refine unit_square_of_composition
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (p ≫ k)))
    (Scheme.Modules.restrictAdjunction p) (Scheme.Modules.restrictAdjunction U.ι)
    (openTensorRestrictionIso p) (openTensorRestrictionIso U.ι)
    (Scheme.Modules.tensorPullbackCompositionIso p k (p ≫ k) rfl)
    (Scheme.Modules.tensorPullbackCompositionIso q U.ι (p ≫ k) pullback.condition.symm)
    (Scheme.Modules.pushforwardComp p k ≪≫ Scheme.Modules.pushforwardCongr rfl)
    (Scheme.Modules.pushforwardComp q U.ι ≪≫
      Scheme.Modules.pushforwardCongr pullback.condition.symm)
    (openTensorRestrictionSquareIso k U) M
    (open_unit p _) (open_unit U.ι M)
    (composition_unit p k (p ≫ k) rfl M)
    (composition_unit q U.ι (p ≫ k) pullback.condition.symm M) ?_
  simp only [openTensorRestrictionSquareIso, p, q, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.hom_inv_id_app_assoc]

end

/-- The underived open tensor square preserves the adjunction unit on stalks.

Proof: expand openTensorRestrictionSquareIso into its four factors. The first
factor converts restriction to tensor pullback along the open projection. The
identity unit_leftAdjointUniq_hom_app identifies the unit of this comparison
with the ordinary restriction unit, whose section formula is restriction.
The next two factors compare successive tensor pullbacks with pullback along
the composite morphism. Apply unit_conjugateEquiv_symm to each composition
mate. The composite units agree after the pushforward composition comparisons,
because pullback.condition identifies the two morphisms to X. The last factor
converts tensor pullback along U.ι back to restriction. Its leftAdjointUniq
unit identity turns the input section into its restriction to U. Naturality
of the unit for pullback.snd moves this last comparison through that unit.
Thus the four factors carry the restricted unit section for k to the unit
section for pullback.snd applied to the restricted input section.
Apply the additive stalk functor and stalkPushforward to this section equation.
The formulas stalkFunctor_map_germ_apply and stalkPushforward_germ_apply turn
these maps into germs of the respective unit sections. The inverse restriction
stalk germ formula identifies each inverse restriction with the germ of the
restricted section, and stalkCongr transports the original input point using
pullback.condition. Every input stalk element is a section germ, so equality
on these representatives gives equality of the additive maps below.
This statement uses no base-change square, tensor coordinates, complexes or
homology. Empty opens have no z0; identity opens and zero modules satisfy the
same unit and germ equations.
Source: Stacks Project, Tag 0096 (lemma-adjoint-pullback-pushforward-modules),
Tag 0098 (lemma-stalk-pullback-modules); Mathlib adjunction mate unit identities.
(blueprint: lem-pc-open-tensor-restriction-square-stalk-unit). -/
theorem openTensorRestrictionSquare_stalk_unit
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (M : X.Modules) (z0 : (pullback k U.ι : Scheme.{u})) :
    let z := pullback.fst k U.ι z0
    let q := pullback.snd k U.ι
    let N := (Scheme.Modules.restrictFunctor U.ι).obj M
    let L0 := RingedSpace.moduleStalkFunctor (pullback k U.ι).toRingedSpace z0
    let F0 := forget₂ (ModuleCat.{u} ((pullback k U.ι).presheaf.stalk z0)) AddCommGrpCat.{u}
    let hp : k z = U.ι (q z0) :=
      congrArg (fun h : pullback k U.ι ⟶ X ↦ h z0) pullback.condition
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k z)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)) ≫
      ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
        AddCommGrpCat.{u} k.base z ≫
      (Scheme.Modules.restrictStalkNatIso (pullback.fst k U.ι) z0).inv.app
        ((Scheme.Modules.tensorPullback k).obj M) ≫
      F0.map (L0.map ((openTensorRestrictionSquareIso k U).hom.app M)) =
    (M.presheaf.stalkCongr (.of_eq hp)).hom ≫
      (Scheme.Modules.restrictStalkNatIso U.ι (q z0)).inv.app M ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (q z0)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)).unit.app N)) ≫
      ((Scheme.Modules.tensorPullback q).obj N).presheaf.stalkPushforward
        AddCommGrpCat.{u} q.base z0 := by
  dsimp only
  exact openRestriction_stalk_square k U M ((Scheme.Modules.tensorPullback k).obj M)
    ((Scheme.Modules.tensorPullback (pullback.snd k U.ι)).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj M))
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (pullback.snd k U.ι))).unit.app ((Scheme.Modules.restrictFunctor U.ι).obj M))
    ((openTensorRestrictionSquareIso k U).hom.app M) (square_unit k U M) z0

end AlgebraicGeometry.SingleComplexBaseChange
