/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # The underived mate on pointed neighbourhood sections -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the restriction comparison unit equation.
-- Adapted from the proved helper in EtaleChartSectionsObjectComparison.
private theorem restriction_unit
    {T Y : Scheme.{v}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit.app F).hom.app (op b) ≫
        ((upperStar AddCommGrpCat.{v + 1} f).obj F).obj.map ψ.op ≫
        ((upperStarIsoLocalizationRestriction AddCommGrpCat.{v + 1} f inferInstance).hom.app
          F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  let A := AddCommGrpCat.{v + 1}
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
    {T Y R : Scheme.{v}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology AddCommGrpCat.{v + 1})
    (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} t).unit.app F).hom.app (op b) ≫
        ((upperStar AddCommGrpCat.{v + 1} t).obj F).obj.map ψ.op ≫
        ((upperStarComp AddCommGrpCat.{v + 1} f g t ht).hom.app F).hom.app (op c) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} g).unit.app F).hom.app (op b) ≫
        ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit.app
          ((upperStar AddCommGrpCat.{v + 1} g).obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((upperStar AddCommGrpCat.{v + 1} f).obj
          ((upperStar AddCommGrpCat.{v + 1} g).obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  let A := AddCommGrpCat.{v + 1}
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

-- Works for any chosen global-sections right adjoint, rather than only the
-- instance constructed from a terminal object. The explicit instance is essential.
private lemma terminalEvaluation_map_eq_res_forAdjoint {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] [HasGlobalSectionsFunctor J A]
    {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) {S : C} (f : S ⟶ T) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F ≫ F.obj.map f.op =
      F.ΓRes (op S) := by
  have he : (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
    simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
      Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom,
      conjugateEquiv_apply_app]
    dsimp
    erw [Adjunction.homEquiv_counit]
    erw [Adjunction.homEquiv_unit]
    simp [constantSheafAdj, Adjunction.comp_unit_app]
  rw [he]
  exact Sheaf.ΓRes_map F f.op

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem globalSectionsUpperStarMap_eval {T Y : Scheme.{v}} (m : T ⟶ Y)
    (FV : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    let A := AddCommGrpCat.{v + 1}
    let wU : T.Etale := Scheme.Etale.mk (𝟙 T)
    let wV : Y.Etale := Scheme.Etale.mk (𝟙 Y)
    let K := (upperStar A m).obj FV
    let tU := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology A
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) T)
    let tV := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) Y)
    let theta : wU ⟶ m.Etale.obj wV :=
      MorphismProperty.Over.homMk (pullback.lift m (𝟙 T)
      ((Category.comp_id m).trans (Category.id_comp m).symm))
      (by change _ ≫ pullback.snd _ _ = _; simp only [pullback.lift_snd]; rfl)
    globalSectionsUpperStarMap A m FV ≫ tU.hom.app K =
      tV.hom.app FV ≫ ((upperStarLowerStarAdjunction A m).unit.app FV).hom.app (op wV) ≫
        K.obj.map theta.op := by
  dsimp only
  let A := AddCommGrpCat.{v + 1}
  let wU : T.Etale := Scheme.Etale.mk (𝟙 T)
  let wV : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let K := (upperStar A m).obj FV
  let tU := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) T)
  let tV := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) Y)
  let theta : wU ⟶ m.Etale.obj wV :=
    MorphismProperty.Over.homMk (pullback.lift m (𝟙 T)
      ((Category.comp_id m).trans (Category.id_comp m).symm))
      (by change _ ≫ pullback.snd _ _ = _; simp only [pullback.lift_snd]; rfl)
  change globalSectionsUpperStarMap A m FV ≫ tU.hom.app K = tV.hom.app FV ≫ _
  let a : wV ⟶ ⊤_ Y.Etale := terminal.from _
  let c : wU ⟶ ⊤_ T.Etale := terminal.from _
  have hEvalU : tU.hom.app K = K.ΓRes (op wU) := by
    have h := terminalEvaluation_map_eq_res_forAdjoint _ _
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) T) K (𝟙 wU)
    rw [op_id] at h
    erw [K.obj.map_id, Category.comp_id] at h
    exact h
  have hEvalV : tV.hom.app FV = FV.ΓRes (op wV) := by
    have h := terminalEvaluation_map_eq_res_forAdjoint _ _
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) Y) FV (𝟙 wV)
    rw [op_id] at h
    erw [FV.obj.map_id, Category.comp_id] at h
    exact h
  have hEvalTerm : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app K =
      K.ΓRes (op (⊤_ T.Etale)) := by
    simpa using terminalEvaluation_map_eq_res_forAdjoint _ _ terminalIsTerminal K
      (𝟙 (⊤_ T.Etale))
  have hEvalTermV : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app FV =
      FV.ΓRes (op (⊤_ Y.Etale)) := by
    simpa using terminalEvaluation_map_eq_res_forAdjoint _ _ terminalIsTerminal FV
      (𝟙 (⊤_ Y.Etale))
  have hG : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
      K.ΓRes (op wU) = K.obj.map c.op := by
    erw [← Sheaf.ΓRes_map K c.op, ← hEvalTerm]
    simp only [Iso.inv_hom_id_app_assoc]
  have hterm : c ≫ (PreservesTerminal.iso m.Etale).inv =
      theta ≫ (MorphismProperty.Over.pullback @Etale ⊤ m).map a := by
    exact (terminalIsTerminal.isTerminalObj m.Etale).hom_ext _ _
  simp only [globalSectionsUpperStarMap, hEvalU, hEvalV, Category.assoc]
  erw [hEvalTermV]
  change FV.ΓRes (op (⊤_ Y.Etale)) ≫
    ((upperStarLowerStarAdjunction A m).unit.app FV).hom.app _ ≫
    K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
    K.ΓRes (op wU) = _
  erw [hG]
  have hmaps : K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫ K.obj.map c.op =
      K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ m).map a).op ≫
        K.obj.map theta.op := by
    rw [← Functor.map_comp, ← op_comp, hterm, op_comp, Functor.map_comp]
  erw [hmaps]
  have hn := ((upperStarLowerStarAdjunction A m).unit.app FV).hom.naturality a.op
  change FV.obj.map a.op ≫ _ = _ ≫
    K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ m).map a).op at hn
  erw [← reassoc_of% hn]
  erw [← Sheaf.ΓRes_map FV a.op]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem pointedSections_pullback {T X : Scheme.{v}} (a : T ⟶ X)
    (V : X.Etale) (m : T ⟶ V.left) (ha : a = m ≫ V.hom)
    (ψ : Scheme.Etale.mk (𝟙 T) ⟶ a.Etale.obj V)
    (hm : ψ.left ≫ pullback.fst V.hom a = m)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app F).hom.app (op V) ≫
      ((upperStar AddCommGrpCat.{v + 1} a).obj F).obj.map ψ.op ≫
        (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology AddCommGrpCat.{v + 1}
          (MorphismProperty.Over.mkIdTerminal (P := @Etale) T)).inv.app _ =
    (etaleObjectSectionsIso V).hom.app F ≫
      globalSectionsUpperStarMap AddCommGrpCat.{v + 1} m
        ((upperStar AddCommGrpCat.{v + 1} V.hom).obj F) ≫
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}).map
        ((upperStarComp AddCommGrpCat.{v + 1} m V.hom a ha).inv.app F) := by
  let A := AddCommGrpCat.{v + 1}
  let wT : T.Etale := Scheme.Etale.mk (𝟙 T)
  let wV : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let FV := (upperStar A V.hom).obj F
  let FT := (upperStar A a).obj F
  let K := (upperStar A m).obj FV
  let eV : (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.hom)).obj wV ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [wV])
  let rV := (upperStarIsoLocalizationRestriction A V.hom inferInstance).app F
  let tV := Sheaf.ΓNatIsoSheafSections V.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left)
  let tT := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) T)
  let δ : wV ⟶ V.hom.Etale.obj V :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) (by rfl))
      (by change _ ≫ pullback.snd _ _ = _; simp [wV])
  let θ : wT ⟶ m.Etale.obj wV :=
    MorphismProperty.Over.homMk (pullback.lift m (𝟙 T)
      ((Category.comp_id m).trans (Category.id_comp m).symm))
      (by change _ ≫ pullback.snd _ _ = _; simp only [pullback.lift_snd]; rfl)
  let c := (upperStarComp A m V.hom a ha).app F
  have hδ := restriction_unit V.hom F V wV δ
  have hδmap : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ V.hom inferInstance
      _root_.trivial).homEquiv wV V).symm δ = eV.hom := by
    ext
    simp [δ, eV, Adjunction.homEquiv_counit]
  rw [hδmap] at hδ
  have hδ' : ((upperStarLowerStarAdjunction A V.hom).unit.app F).hom.app (op V) ≫
      FV.obj.map δ.op = F.obj.map eV.hom.op ≫ rV.inv.hom.app (op wV) := by
    apply (cancel_mono (rV.hom.hom.app (op wV))).1
    simp only [Category.assoc]
    have hr : rV.inv.hom.app (op wV) ≫ rV.hom.hom.app (op wV) = 𝟙 _ :=
      congrArg (fun z ↦ z.hom.app (op wV)) rV.inv_hom_id
    conv_rhs => rw [hr]
    erw [Category.comp_id]
    exact hδ
  have hψ : ψ.left ≫ pullback.snd V.hom a = 𝟙 T := ψ.w
  have hχ : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      m V.hom a ha).hom.app V = θ ≫ m.Etale.map δ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ _ = θ.left ≫ _
    dsimp only [Scheme.Hom.Etale]
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    have hs : ((MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V).hom =
        pullback.snd V.hom V.hom := rfl
    dsimp only [MorphismProperty.Over.pullback_obj_hom]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [θ, δ, MorphismProperty.Over.homMk_hom, Over.homMk_left,
          MorphismProperty.Over.mk_left, Functor.const_obj_obj, Functor.id_obj,
          MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.pullback_obj_hom,
          Functor.comp_obj, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
          wV, MorphismProperty.Over.mk_hom, pullback.lift_fst_assoc,
          limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id, hm]
      · dsimp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk, Functor.comp_obj]
        simp only [θ, δ, MorphismProperty.Over.homMk_hom, Over.homMk_left,
          Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
          pullback.lift_fst, pullback.lift_snd]
        simp only [pullback.map, pullback.lift_snd_assoc, pullback.lift_fst_assoc, Category.comp_id]
        rw [← Category.assoc, hψ]
        exact (Category.id_comp m).trans (Category.comp_id m).symm
    · dsimp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk, Functor.comp_obj]
      simp only [θ, MorphismProperty.Over.homMk_hom, Over.homMk_left,
        Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, pullback.lift_snd]
      rw [Category.comp_id, hψ]
  have hc := composition_unit m V.hom a ha F V wT ψ
  rw [hχ, op_comp, Functor.map_comp] at hc
  change _ = ((upperStarLowerStarAdjunction A V.hom).unit.app F).hom.app (op V) ≫
    ((upperStarLowerStarAdjunction A m).unit.app FV).hom.app
      (op (V.hom.Etale.obj V)) ≫ ((lowerStar A m).obj K).obj.map δ.op ≫ K.obj.map θ.op at hc
  erw [← ((upperStarLowerStarAdjunction A m).unit.app FV).hom.naturality_assoc,
    reassoc_of% hδ'] at hc
  have ht := globalSectionsUpperStarMap_eval m FV
  change globalSectionsUpperStarMap A m FV ≫ tT.hom.app K =
    tV.hom.app FV ≫ ((upperStarLowerStarAdjunction A m).unit.app FV).hom.app (op wV) ≫
      K.obj.map θ.op at ht
  have ht' := congrArg (fun z ↦ z ≫ tT.inv.app K) ht
  simp only [Category.assoc, Iso.hom_inv_id_app] at ht'
  erw [Category.comp_id] at ht'
  have hn := tT.inv.naturality c.hom
  change c.hom.hom.app (op wT) ≫ tT.inv.app K =
    tT.inv.app FT ≫ (Sheaf.Γ T.smallEtaleTopology A).map c.hom at hn
  apply (cancel_mono ((Sheaf.Γ T.smallEtaleTopology A).map c.hom)).1
  change _ = (etaleObjectSectionsIso V).hom.app F ≫
    globalSectionsUpperStarMap A m FV ≫ (Sheaf.Γ T.smallEtaleTopology A).map c.inv ≫
      (Sheaf.Γ T.smallEtaleTopology A).map c.hom
  rw [← Functor.map_comp, c.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Category.assoc]
  erw [← hn]
  erw [reassoc_of% hc]
  change _ = (F.obj.map eV.hom.op ≫ rV.inv.hom.app (op wV) ≫ tV.inv.app FV) ≫ _
  rw [ht']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem lowerStarSections_eval {T Y : Scheme.{v}} (h : T ⟶ Y)
    (H : Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    let A := AddCommGrpCat.{v + 1}
    let _wY : Y.Etale := Scheme.Etale.mk (𝟙 Y)
    let _wT : T.Etale := Scheme.Etale.mk (𝟙 T)
    let tY := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) Y)
    let tT := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology A
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) T)
    let e := ((MorphismProperty.Over.mkIdTerminal (P := @Etale) Y).isTerminalObj
      h.Etale).uniqueUpToIso (MorphismProperty.Over.mkIdTerminal (P := @Etale) T)
    tY.inv.app ((lowerStar A h).obj H) ≫ (lowerStarCompGlobalSectionsIso A h).hom.app H =
      H.obj.map e.inv.op ≫ tT.inv.app H := by
  dsimp only
  let A := AddCommGrpCat.{v + 1}
  let wY : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let wT : T.Etale := Scheme.Etale.mk (𝟙 T)
  let tY := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) Y)
  let tT := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) T)
  let e := ((MorphismProperty.Over.mkIdTerminal (P := @Etale) Y).isTerminalObj
    h.Etale).uniqueUpToIso (MorphismProperty.Over.mkIdTerminal (P := @Etale) T)
  let P := (lowerStar A h).obj H
  let a : ⊤_ Y.Etale ⟶ wY := (MorphismProperty.Over.mkIdTerminal (P := @Etale) Y).from _
  let b : ⊤_ T.Etale ⟶ wT := (MorphismProperty.Over.mkIdTerminal (P := @Etale) T).from _
  let c := (PreservesTerminal.iso h.Etale).inv
  have ht : c ≫ h.Etale.map a = b ≫ e.inv :=
    ((MorphismProperty.Over.mkIdTerminal (P := @Etale) Y).isTerminalObj h.Etale).hom_ext _ _
  have hy : tY.inv.app P ≫ P.ΓRes (op (⊤_ Y.Etale)) = P.obj.map a.op := by
    erw [← Sheaf.ΓRes_map P a.op]
    have he := terminalEvaluation_map_eq_res_forAdjoint _ _
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) Y) P (𝟙 wY)
    rw [op_id] at he
    erw [P.obj.map_id, Category.comp_id] at he
    rw [← he]
    change tY.inv.app P ≫ tY.hom.app P ≫ _ = _
    simp only [Iso.inv_hom_id_app_assoc]
  have hz : H.obj.map b.op ≫ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app H =
      tT.inv.app H := by
    apply (cancel_epi (tT.hom.app H)).1
    simp only [← Category.assoc]
    erw [terminalEvaluation_map_eq_res_forAdjoint _ _
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) T) H b]
    have he := terminalEvaluation_map_eq_res_forAdjoint _ _ terminalIsTerminal H (𝟙 (⊤_ T.Etale))
    rw [op_id] at he
    erw [H.obj.map_id, Category.comp_id] at he
    rw [← he]
    exact (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom_inv_id_app H
      |>.trans (tT.hom_inv_id_app H).symm
  change tY.inv.app P ≫ (lowerStarCompGlobalSectionsIso A h).hom.app H = _
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  change tY.inv.app P ≫ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app P ≫
    H.obj.map c.op ≫ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app H = _
  have he := terminalEvaluation_map_eq_res_forAdjoint _ _ terminalIsTerminal P (𝟙 (⊤_ Y.Etale))
  rw [op_id] at he
  erw [P.obj.map_id, Category.comp_id] at he
  rw [he, ← Category.assoc, ← Category.assoc, hy]
  change H.obj.map (h.Etale.map a).op ≫ H.obj.map c.op ≫ _ = _
  have hmap : H.obj.map (h.Etale.map a).op ≫ H.obj.map c.op =
      H.obj.map e.inv.op ≫ H.obj.map b.op := by
    rw [← Functor.map_comp, ← op_comp, ht, op_comp, Functor.map_comp]
  rw [← Category.assoc, hmap, Category.assoc]
  change H.obj.map e.inv.op ≫ H.obj.map b.op ≫
      (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app H = _
  rw [hz]

/-- The underived exchange map evaluated after restriction to the strict-local base.
Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-underived-sections-mate). -/
noncomputable def strictLocalUnderivedMateSections {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    lowerStar AddCommGrpCat.{v + 1} f ⋙
        (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op ((strictLocalNeighbourhoods s).obj i)) ⟶
      upperStar AddCommGrpCat.{v + 1}
          (pullback.fst f (Scheme.strictLocalizationToBase s)) ⋙
        Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
          AddCommGrpCat.{v + 1} :=
  Functor.whiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
      (strictLocalSectionRestrictionNat s i) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictLocalizationToBase s)).toCommSq)
      (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (upperStar AddCommGrpCat.{v + 1}
        (pullback.fst f (Scheme.strictLocalizationToBase s)))
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictLocalizationToBase s))).hom

-- The mate calculation elaborates several nested site-pullback comparisons.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluating the underived mate on sections is restriction along the cone leg.
This is an equality of transformations of sheaves, before complexes or derivation.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-underived-sections-mate).

Proof: expand the restriction on the base as the inverse-image adjunction unit
followed by evaluation at the pointed neighbourhood section. Expand baseChangeMap
as the unit along the second pullback projection, the inverse-image square
comparison, and the counit along f. Naturality of evaluation moves the latter
maps across the neighbourhood section. The two adjunction triangle identities
cancel the intermediate unit and counit. The result is evaluation of f_*F on
the stage, identified by sourceStageSectionsIso, followed by sectionsPullbackNat
along the cone leg and the inverse composition comparison upperStarComp.
Q.first identifies the map on the base with the pointed neighbourhood section;
Q.over identifies the composite projection to X. These equations determine the
map into the scheme pullback, so both evaluations use the same map. All operations
are functorial in F, giving the equality of natural transformations. No etaleness
of the cone leg is needed. The zero sheaf and empty fibre use the same identities. -/
theorem strictLocalUnderivedMateSections_eq {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    strictLocalUnderivedMateSections f s i =
      (sourceStageSectionsIso f s i).hom ≫
        Functor.whiskerLeft
          (upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
          (sectionsPullbackNat (Q.legs.app i)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
            ((strictLocalNeighbourhoodProjection f s).app i)
            (pullback.fst f (Scheme.strictLocalizationToBase s)) (Q.over i).symm).inv
          (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
            AddCommGrpCat.{v + 1}) := by
  apply NatTrans.ext
  funext F
  simp only [strictLocalUnderivedMateSections, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp]
  unfold strictLocalSectionRestrictionNat
  dsimp only [Functor.comp_obj]
  unfold strictHenselizationSectionRestriction
  have hterminal : IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
        (Scheme.strictLocalization s))
      (Scheme.Etale.mk (𝟙 (Scheme.strictLocalization s))) Over.mkIdTerminal =
      MorphismProperty.Over.mkIdTerminal (P := @Etale) (Scheme.strictLocalization s) :=
    Subsingleton.elim _ _
  rw [hterminal]
  let A := AddCommGrpCat.{v + 1}
  let g := Scheme.strictLocalizationToBase s
  let p := pullback.fst f g
  let h := pullback.snd f g
  let W := (strictLocalNeighbourhoods s).obj i
  let U := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let wS := Scheme.Etale.mk (𝟙 (Scheme.strictLocalization s))
  let wX := Scheme.Etale.mk (𝟙 (pullback f g))
  let H := (upperStar A p).obj F
  let G := (upperStar A g).obj ((lowerStar A f).obj F)
  let P := (lowerStar A h).obj H
  let σ := strictHenselizationNeighbourhoodSection s i
  let b := (baseChangeMap A (IsPullback.of_hasPullback f g).toCommSq).app F
  let tS := Sheaf.ΓNatIsoSheafSections (Scheme.strictLocalization s).smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) (Scheme.strictLocalization s))
  let tX := Sheaf.ΓNatIsoSheafSections (pullback f g).smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) (pullback f g))
  let e := ((MorphismProperty.Over.mkIdTerminal (P := @Etale)
    (Scheme.strictLocalization s)).isTerminalObj h.Etale).uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) (pullback f g))
  let c₁ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) p f
  let c₂ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    h g (p ≫ f) (pullback.condition (f := f) (g := g))
  let ψ : wX ⟶ p.Etale.obj U :=
    e.inv ≫ h.Etale.map σ ≫ c₂.inv.app W ≫ c₁.hom.app W
  have ht := tS.inv.naturality b
  change b.hom.app (op wS) ≫ tS.inv.app P =
    tS.inv.app G ≫ (Sheaf.Γ _ A).map b at ht
  have hb := b.hom.naturality σ.op
  have hu := congrArg (fun z ↦ z.hom.app (op W))
    (unit_map_baseChangeMap_app A (IsPullback.of_hasPullback f g).toCommSq F)
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  change ((upperStarLowerStarAdjunction A g).unit.app ((lowerStar A f).obj F)).hom.app
      (op W) ≫ b.hom.app (op (g.Etale.obj W)) =
    ((upperStarLowerStarAdjunction A p).unit.app F).hom.app (op U) ≫
      ((squareLowerStarIso A (IsPullback.of_hasPullback f g).toCommSq).hom.app H).hom.app
        (op W) at hu
  change (((upperStarLowerStarAdjunction A g).unit.app ((lowerStar A f).obj F)).hom.app
      (op W) ≫ G.obj.map σ.op ≫ tS.inv.app G) ≫
    (Sheaf.Γ _ A).map b ≫ (lowerStarCompGlobalSectionsIso A h).hom.app H = _
  simp only [Category.assoc]
  rw [← reassoc_of% ht]
  change _ = _ at hb
  erw [reassoc_of% hb, reassoc_of% hu]
  have he := lowerStarSections_eval h H
  change tS.inv.app P ≫ (lowerStarCompGlobalSectionsIso A h).hom.app H =
    H.obj.map e.inv.op ≫ tX.inv.app H at he
  rw [he]
  change _ ≫ (H.obj.map (c₁.hom.app W).op ≫ H.obj.map (c₂.inv.app W).op) ≫
    H.obj.map (h.Etale.map σ).op ≫ H.obj.map e.inv.op ≫ tX.inv.app H = _
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [← op_comp]
  change ((upperStarLowerStarAdjunction A p).unit.app F).hom.app (op U) ≫
    H.obj.map ψ.op ≫ tX.inv.app H = _
  have hψ : ψ.left ≫ pullback.fst U.hom p = Q.legs.app i := by
    apply pullback.hom_ext
    · change e.inv.left ≫ (h.Etale.map σ).left ≫ (c₂.inv.app W).left ≫
        (c₁.hom.app W).left ≫ pullback.fst U.hom p ≫ pullback.fst W.hom f = _
      dsimp only [c₁, c₂, Scheme.Hom.Etale]
      simp only [MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Over.pullbackComp_inv_app_left,
        MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
      erw [pullbackLeftPullbackSndIso_inv_fst W.hom f p]
      simp only [pullback.map, pullback.lift_fst, Category.comp_id]
      erw [pullbackLeftPullbackSndIso_hom_fst W.hom g h]
      erw [pullback.lift_fst_assoc]
      have hσ : σ.left ≫ pullback.fst W.hom g =
          (Scheme.strictHenselizationAffineCone s).π.app (op (op i)) ≫
            Spec.map (Scheme.ΓSpecIso
              ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
                i).1.left.unop).inv := by
        exact pullback.lift_fst _ _ _
      simp only [Category.assoc]
      rw [hσ, Q.first]
      have hew := e.inv.w
      change e.inv.left ≫ pullback.snd (𝟙 _) h = 𝟙 _ at hew
      have hfst : pullback.fst (𝟙 _) h = pullback.snd (𝟙 _) h ≫ h := by
        simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 _) (g := h))
      erw [hfst]
      simp only [Category.assoc]
      erw [reassoc_of% hew]
    · have hw := ψ.w
      change ψ.left ≫ pullback.snd U.hom p = 𝟙 _ at hw
      change (ψ.left ≫ pullback.fst U.hom p) ≫ U.hom = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
      exact (Category.id_comp p).trans (Q.over i).symm
  have hp := pointedSections_pullback p U (Q.legs.app i) (Q.over i).symm ψ hψ F
  change _ = (etaleObjectSectionsIso U).hom.app F ≫
    globalSectionsUpperStarMap A (Q.legs.app i) ((upperStar A U.hom).obj F) ≫
      (Sheaf.Γ (pullback f g).smallEtaleTopology A).map
        ((upperStarComp A (Q.legs.app i) U.hom p (Q.over i).symm).inv.app F) at hp
  rw [hp]
  have hs : (etaleObjectSectionsIso U).hom.app F =
      (sourceStageSectionsIso f s i).hom.app F := by
    unfold etaleObjectSectionsIso sourceStageSectionsIso
    congr 1
  rw [hs]
  congr 2
  unfold sectionsPullbackNat globalSectionsUpperStarMap lowerStarCompGlobalSectionsIso
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Iso.trans_hom, Iso.symm_hom]
  rw [← (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.naturality_assoc]
  rfl


end AlgebraicGeometry.Etale
