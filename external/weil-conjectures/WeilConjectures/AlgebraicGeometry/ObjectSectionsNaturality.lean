/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the restriction comparison unit equation.
-- Adapted from the proved helper in EtaleChartSectionsObjectComparison.
private theorem restriction_unit
    {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F).hom.app (op b) ≫
        ((upperStar AddCommGrpCat.{u + 1} f).obj F).obj.map ψ.op ≫
        ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f inferInstance).hom.app
          F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  let A := AddCommGrpCat.{u + 1}
  let ρ := (upperStarIsoLocalizationRestriction A f inferInstance).hom.app F
  have hu := congrArg (fun α ↦ α.hom.app (op b))
    (Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A f)
      (localizationRestrictionLowerStarAdjunction A f inferInstance) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  rw [ρ.hom.naturality, ← Category.assoc]
  erw [show ((upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
    ρ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj b)) =
    ((localizationRestrictionLowerStarAdjunction A f inferInstance).unit.app F).hom.app
      (op b) from hu]
  change (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the composition unit equation, after restriction.
-- Adapted from the proved helper in EtaleChartSectionsObjectComparison.
private theorem composition_unit
    {T Y R : Scheme.{u}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app F).hom.app (op b) ≫
        ((upperStar AddCommGrpCat.{u + 1} t).obj F).obj.map ψ.op ≫
        ((upperStarComp AddCommGrpCat.{u + 1} f g t ht).hom.app F).hom.app (op c) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F).hom.app (op b) ≫
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
          ((upperStar AddCommGrpCat.{u + 1} g).obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((upperStar AddCommGrpCat.{u + 1} f).obj
          ((upperStar AddCommGrpCat.{u + 1} g).obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  let A := AddCommGrpCat.{u + 1}
  have h := congrArg (fun α ↦ α.hom.app (op b))
    (upperStarComp_hom_app_unit_app A f g F t ht)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at h
  rw [((upperStarComp A f g t ht).hom.app F).hom.naturality, ← Category.assoc]
  erw [h]
  simp only [Functor.comp_obj, Iso.symm_inv, lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]
  rfl

-- Generalized to restriction along any arrow into a terminal object.
-- The pointwise equality in EtaleObjectSections is private to that module.
private lemma terminalEvaluation_map_eq_res {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) {S : C} (f : S ⟶ T) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F ≫ F.obj.map f.op =
      F.ΓRes (op S) := by
  have he : (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
    simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
      Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
    dsimp
    erw [Adjunction.homEquiv_counit]
    erw [Adjunction.homEquiv_unit]
    simp [constantSheafAdj, Adjunction.comp_unit_app]
  rw [he]
  exact Sheaf.ΓRes_map F f.op

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of object sections under an étale arrow.
Source: Stacks Project, Tags 03Q9 and 03S2; this is the pointwise
comparison after evaluation at the identity étale object.
Proof: expand the two comparison maps, use adjunction-unit naturality and
pullback hom_ext for the defining square.
(blueprint: lem-weil-pbc-object-sections-naturality) -/
theorem objectSections_naturality {X : Scheme.{v}} {U V : X.Etale}
    (b : U ⟶ V) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    F.obj.map b.op ≫ (etaleObjectSectionsIso U).hom.app F ≫
      (Sheaf.Γ U.left.smallEtaleTopology AddCommGrpCat.{v + 1}).map
        ((upperStarComp AddCommGrpCat.{v + 1} b.left V.hom U.hom b.w.symm).hom.app F) =
    (etaleObjectSectionsIso V).hom.app F ≫
      globalSectionsUpperStarMap AddCommGrpCat.{v + 1} b.left
        ((upperStar AddCommGrpCat.{v + 1} V.hom).obj F)  := by
  let A := AddCommGrpCat.{v + 1}
  let wU : U.left.Etale := Scheme.Etale.mk (𝟙 U.left)
  let wV : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eU : (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.hom)).obj wU ≅ U :=
    MorphismProperty.Over.isoMk (Iso.refl U.left) (by simp [wU])
  let eV : (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.hom)).obj wV ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [wV])
  let FU := (upperStar A U.hom).obj F
  let FV := (upperStar A V.hom).obj F
  let K := (upperStar A b.left).obj FV
  let rU := (upperStarIsoLocalizationRestriction A U.hom inferInstance).app F
  let rV := (upperStarIsoLocalizationRestriction A V.hom inferInstance).app F
  let tU := Sheaf.ΓNatIsoSheafSections U.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) U.left)
  let tV := Sheaf.ΓNatIsoSheafSections V.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left)
  let delta : wV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) (by simp))
      (by simp [wV])
  let gamma : wU ⟶ (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift b.left (𝟙 U.left) (b.w.trans (Category.id_comp U.hom).symm))
      (by simp [wU])
  let theta : wU ⟶ (MorphismProperty.Over.pullback @Etale ⊤ b.left).obj wV :=
    MorphismProperty.Over.homMk (pullback.lift b.left (𝟙 U.left)
      ((Category.comp_id b.left).trans (Category.id_comp b.left).symm))
      (by simp [wU])
  have hγ := restriction_unit U.hom F V wU gamma
  have hγmap : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ U.hom inferInstance
      _root_.trivial).homEquiv wU V).symm gamma = eU.hom ≫ b := by
    ext
    simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.map_obj_left,
      Adjunction.homEquiv_counit, MorphismProperty.Over.mapPullbackAdj_counit_app,
      MorphismProperty.Comma.comp_hom, MorphismProperty.Over.homMk_hom, Comma.comp_left,
      MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.map_map_left,
      Over.homMk_left, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      MorphismProperty.Over.isoMk_hom_left, Iso.refl_hom, gamma, eU]
    exact (Category.id_comp b.left).symm
  rw [hγmap, op_comp, Functor.map_comp] at hγ
  have hγ' : ((upperStarLowerStarAdjunction A U.hom).unit.app F).hom.app (op V) ≫
      FU.obj.map gamma.op = F.obj.map b.op ≫ F.obj.map eU.hom.op ≫
        rU.inv.hom.app (op wU) := by
    have hr : rU.inv.hom.app (op wU) ≫ rU.hom.hom.app (op wU) = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app (op wU)) rU.inv_hom_id
    apply (cancel_mono (rU.hom.hom.app (op wU))).1
    simp only [Category.assoc]
    conv_rhs => rw [hr]
    erw [Category.comp_id]
    exact hγ
  have hδ := restriction_unit V.hom F V wV delta
  have hδmap : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ V.hom inferInstance
      _root_.trivial).homEquiv wV V).symm delta = eV.hom := by
    apply MorphismProperty.Over.Hom.ext
    simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.map_obj_left,
      Adjunction.homEquiv_counit, MorphismProperty.Over.mapPullbackAdj_counit_app,
      MorphismProperty.Comma.comp_hom, MorphismProperty.Over.homMk_hom, Comma.comp_left,
      MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.map_map_left,
      Over.homMk_left, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      MorphismProperty.Over.isoMk_hom_left, Iso.refl_hom, delta, eV]
  rw [hδmap] at hδ
  have hδ' : ((upperStarLowerStarAdjunction A V.hom).unit.app F).hom.app (op V) ≫
      FV.obj.map delta.op = F.obj.map eV.hom.op ≫ rV.inv.hom.app (op wV) := by
    have hr : rV.inv.hom.app (op wV) ≫ rV.hom.hom.app (op wV) = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app (op wV)) rV.inv_hom_id
    apply (cancel_mono (rV.hom.hom.app (op wV))).1
    simp only [Category.assoc]
    conv_rhs => rw [hr]
    erw [Category.comp_id]
    exact hδ
  have hχ : gamma ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      b.left V.hom U.hom b.w.symm).hom.app V =
      theta ≫ (MorphismProperty.Over.pullback @Etale ⊤ b.left).map delta := by
    apply MorphismProperty.Over.Hom.ext
    change gamma.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      b.left V.hom U.hom b.w.symm).hom.app V).left =
        theta.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ b.left).map delta).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk, Functor.comp_obj, gamma, theta, delta,
          MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc,
          pullbackLeftPullbackSndIso_inv_fst,
          pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
        exact (Category.comp_id b.left).symm
      · simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk, Functor.comp_obj, gamma, theta, delta,
          MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc,
          pullbackLeftPullbackSndIso_inv_fst_snd,
          pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst_assoc,
          Category.comp_id]
        exact (Category.id_comp b.left).trans (Category.comp_id b.left).symm
    · simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, Functor.comp_obj, gamma, theta,
        MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc,
        pullbackLeftPullbackSndIso_inv_snd_snd,
        pullback.lift_snd, pullback.lift_snd_assoc]
      exact Category.id_comp _
  have hc := composition_unit b.left V.hom U.hom b.w.symm F V wU gamma
  rw [hχ, op_comp, Functor.map_comp] at hc
  change _ = ((upperStarLowerStarAdjunction A V.hom).unit.app F).hom.app (op V) ≫
    ((upperStarLowerStarAdjunction A b.left).unit.app FV).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V)) ≫
    ((lowerStar A b.left).obj K).obj.map delta.op ≫ K.obj.map theta.op at hc
  erw [← ((upperStarLowerStarAdjunction A b.left).unit.app FV).hom.naturality_assoc,
    reassoc_of% hδ', reassoc_of% hγ'] at hc
  have ht : globalSectionsUpperStarMap A b.left FV ≫ tU.hom.app K =
      tV.hom.app FV ≫ ((upperStarLowerStarAdjunction A b.left).unit.app FV).hom.app (op wV) ≫
        K.obj.map theta.op := by
    let a : wV ⟶ ⊤_ V.left.Etale := terminal.from _
    let c : wU ⟶ ⊤_ U.left.Etale := terminal.from _
    have hEvalU : tU.hom.app K = K.ΓRes (op wU) := by
      have h := terminalEvaluation_map_eq_res _ _
        (MorphismProperty.Over.mkIdTerminal (P := @Etale) U.left) K (𝟙 wU)
      rw [op_id] at h
      erw [K.obj.map_id, Category.comp_id] at h
      exact h
    have hEvalV : tV.hom.app FV = FV.ΓRes (op wV) := by
      have h := terminalEvaluation_map_eq_res _ _
        (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left) FV (𝟙 wV)
      rw [op_id] at h
      erw [FV.obj.map_id, Category.comp_id] at h
      exact h
    have hEvalTerm : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app K =
        K.ΓRes (op (⊤_ U.left.Etale)) := by
      simpa using terminalEvaluation_map_eq_res _ _ terminalIsTerminal K
        (𝟙 (⊤_ U.left.Etale))
    have hEvalTermV : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app FV =
        FV.ΓRes (op (⊤_ V.left.Etale)) := by
      simpa using terminalEvaluation_map_eq_res _ _ terminalIsTerminal FV
        (𝟙 (⊤_ V.left.Etale))
    have hG : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
        K.ΓRes (op wU) = K.obj.map c.op := by
      erw [← Sheaf.ΓRes_map K c.op, ← hEvalTerm]
      simp only [Iso.inv_hom_id_app_assoc]
    have hterm : c ≫ (PreservesTerminal.iso b.left.Etale).inv =
        theta ≫ (MorphismProperty.Over.pullback @Etale ⊤ b.left).map a := by
      exact (terminalIsTerminal.isTerminalObj b.left.Etale).hom_ext _ _
    simp only [globalSectionsUpperStarMap, hEvalU, hEvalV, Category.assoc]
    erw [hEvalTermV]
    change FV.ΓRes (op (⊤_ V.left.Etale)) ≫
      ((upperStarLowerStarAdjunction A b.left).unit.app FV).hom.app _ ≫
      K.obj.map (PreservesTerminal.iso b.left.Etale).inv.op ≫
      (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
      K.ΓRes (op wU) = _
    erw [hG]
    have hmaps : K.obj.map (PreservesTerminal.iso b.left.Etale).inv.op ≫ K.obj.map c.op =
        K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ b.left).map a).op ≫
          K.obj.map theta.op := by
      rw [← Functor.map_comp, ← op_comp, hterm, op_comp, Functor.map_comp]
    erw [hmaps]
    have hn := ((upperStarLowerStarAdjunction A b.left).unit.app FV).hom.naturality a.op
    change FV.obj.map a.op ≫ _ = _ ≫
      K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ b.left).map a).op at hn
    erw [← reassoc_of% hn]
    erw [← Sheaf.ΓRes_map FV a.op]
    rfl
  let c := (upperStarComp A b.left V.hom U.hom b.w.symm).hom.app F
  have hn := tU.inv.naturality c
  change c.hom.app (op wU) ≫ tU.inv.app K =
    tU.inv.app FU ≫ (Sheaf.Γ U.left.smallEtaleTopology A).map c at hn
  have ht' : globalSectionsUpperStarMap A b.left FV =
      tV.hom.app FV ≫ ((upperStarLowerStarAdjunction A b.left).unit.app FV).hom.app
        (op wV) ≫ K.obj.map theta.op ≫ tU.inv.app K := by
    apply (cancel_mono (tU.hom.app K)).1
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact ht
  change F.obj.map b.op ≫
    (F.obj.map eU.hom.op ≫ rU.inv.hom.app (op wU) ≫ tU.inv.app FU) ≫
      (Sheaf.Γ U.left.smallEtaleTopology A).map c =
    (F.obj.map eV.hom.op ≫ rV.inv.hom.app (op wV) ≫ tV.inv.app FV) ≫
      globalSectionsUpperStarMap A b.left FV
  rw [ht']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← hn]
  simpa only [Category.assoc] using congrArg (· ≫ tU.inv.app K) hc

end AlgebraicGeometry.Etale
