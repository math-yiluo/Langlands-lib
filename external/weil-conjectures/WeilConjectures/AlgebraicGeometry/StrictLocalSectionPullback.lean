/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Pullback of strict-local representative sections

Source: Stacks Project, Tags 03Q9 and 0A3U.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private lemma terminalEvaluation_eq_res_local {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) (_unused : True) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  dsimp
  erw [Adjunction.homEquiv_counit]
  erw [Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem terminal_pullback_formula
    (Λ : Type (u + 1)) [CommRing Λ] {Z W : Scheme.{u}} (q : W ⟶ Z)
    (H : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (δ : Scheme.Etale.mk (𝟙 W) ⟶ q.Etale.obj (Scheme.Etale.mk (𝟙 Z))) :
    globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
      (Sheaf.ΓNatIsoSheafSections _ _ (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ W)
        (Scheme.Etale.mk (𝟙 W)) Over.mkIdTerminal)).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) q).obj H) =
    (Sheaf.ΓNatIsoSheafSections _ _ (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ Z)
      (Scheme.Etale.mk (𝟙 Z)) Over.mkIdTerminal)).hom.app H ≫
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app H).hom.app
      (op (Scheme.Etale.mk (𝟙 Z))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ) q).obj H).obj.map δ.op := by
  let K := (upperStar (ModuleCat.{u + 1} Λ) q).obj H
  let a : Scheme.Etale.mk (𝟙 Z) ⟶ ⊤_ Z.Etale := terminal.from _
  let c : Scheme.Etale.mk (𝟙 W) ⟶ ⊤_ W.Etale := terminal.from _
  have hK : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
      K.ΓRes (op (Scheme.Etale.mk (𝟙 W))) = K.obj.map c.op := by
    erw [← Sheaf.ΓRes_map K c.op,
      ← terminalEvaluation_eq_res_local _ _ terminalIsTerminal K trivial]
    simp only [Iso.inv_hom_id_app_assoc]
  have hterm : c ≫ (PreservesTerminal.iso q.Etale).inv = δ ≫ q.Etale.map a :=
    (terminalIsTerminal.isTerminalObj q.Etale).hom_ext _ _
  simp only [globalSectionsUpperStarMap, Category.assoc]
  simp only [terminalEvaluation_eq_res_local _ _ _ _ trivial]
  change H.ΓRes (op (⊤_ Z.Etale)) ≫
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app H).hom.app _ ≫
    K.obj.map (PreservesTerminal.iso q.Etale).inv.op ≫
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
    K.ΓRes (op (Scheme.Etale.mk (𝟙 W))) = _
  erw [hK]
  have hmaps : K.obj.map (PreservesTerminal.iso q.Etale).inv.op ≫ K.obj.map c.op =
      K.obj.map (q.Etale.map a).op ≫ K.obj.map δ.op := by
    rw [← Functor.map_comp, ← op_comp, hterm, op_comp, Functor.map_comp]
  erw [hmaps]
  have hn := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app H).hom.naturality
    a.op
  change H.obj.map a.op ≫ _ = _ ≫ K.obj.map (q.Etale.map a).op at hn
  erw [← reassoc_of% hn]
  erw [← Sheaf.ΓRes_map H a.op]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem composite_unit
    (Λ : Type (u + 1)) [CommRing Λ] {X Z W : Scheme.{u}}
    (q : W ⟶ Z) (p : Z ⟶ X) (g : W ⟶ X) (hg : g = q ≫ p)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F ≫
      (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app
          ((upperStar (ModuleCat.{u + 1} Λ) p).obj F)) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) q p g hg).hom.app _ ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q p g hg).inv.app F) =
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F := by
  have hu := upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) q p F g hg
  have hh := congrArg (fun a ↦ a ≫ (lowerStar (ModuleCat.{u + 1} Λ) g).map
    ((upperStarComp (ModuleCat.{u + 1} Λ) q p g hg).inv.app F)) hu
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Adjunction.comp_unit_app] at hh
  rw [(lowerStar (ModuleCat.{u + 1} Λ) g).map_id] at hh
  exact hh.symm.trans (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
private theorem pre_composite_unit
    (Λ : Type (u + 1)) [CommRing Λ] {X Z W : Scheme.{u}}
    (q : W ⟶ Z) (p : Z ⟶ X) (g : W ⟶ X) (hg : g = q ≫ p)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F ≫
      (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app
          ((upperStar (ModuleCat.{u + 1} Λ) p).obj F) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) q).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) q p g hg).inv.app F)) =
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) q p g hg).inv.app _ := by
  apply (cancel_mono ((lowerStarComp (ModuleCat.{u + 1} Λ) q p g hg).hom.app
    ((upperStar (ModuleCat.{u + 1} Λ) g).obj F))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
  have hn := (lowerStarComp (ModuleCat.{u + 1} Λ) q p g hg).hom.naturality
    ((upperStarComp (ModuleCat.{u + 1} Λ) q p g hg).inv.app F)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  exact (composite_unit Λ q p g hg F).trans (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Pulling a strict-local representative section back to the pointed fibre is the
unit restriction along that representative's marked point.
Source: Stacks Project, Tag 03Q9, canonical restriction on representatives, and
Tag 0A3U, degree-zero compatibility in the parent factorization.
(blueprint: lem-weil-pbc-strict-local-section-pullback).

Proof: expand `qcqsStrictLocalSectionRestriction` and the global-sections pullback.
Naturality of terminal evaluation changes the latter into the unit for q followed
by restriction along its terminal lift. Naturality of the unit moves the strict-local
limit-leg restriction past this unit. The composition-unit identity and the inverse
of `upperStarComp` identify the two successive inverse-image units with the unit for
g'. The remaining morphism from the terminal object to g'^*f^*V has outer second
projection identity. Its inner projections are g', by hq, and f' followed by the
marked point: use hqt to replace the map to the strict-local base by f't, then use
hpoint to replace t followed by the limit leg by the marked point. Pullback hom-ext
therefore identifies this morphism with `geometricFibreSectionLift`. The terminal
section/global-section isomorphisms cancel, leaving exactly the stated identity.
No isomorphism of stalks, comparison map a, qcqs hypothesis, or exchange map occurs.
The argument is valid for empty schemes and zero coefficient modules as well. -/
theorem strictLocal_section_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictLocalization s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationAffineCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictLocalizationToBase s))
    (hqt : q ≫ pullback.snd f (Scheme.strictLocalizationToBase s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictLocalizationToBase s) = g')
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    qcqsStrictLocalSectionRestriction Λ f s F j ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictLocalizationToBase s)) g' hq.symm).inv.app F) =
      geometricFibreSectionRestriction Λ sq F
        ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
            ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) := by
  classical
  let p := pullback.fst f (Scheme.strictLocalizationToBase s)
  let H := (upperStar (ModuleCat.{u + 1} Λ) p).obj F
  let K := (upperStar (ModuleCat.{u + 1} Λ) q).obj H
  let G := (upperStar (ModuleCat.{u + 1} Λ) g').obj F
  let V := (Scheme.AffineEtale.Spec Y).obj
    ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1
  let U := f.Etale.obj V
  let δ := qcqsStrictLocalNeighbourhoodSection f s j
  let θ : Scheme.Etale.mk (𝟙 X') ⟶ q.Etale.obj (Scheme.Etale.mk (𝟙 _)) :=
    MorphismProperty.Over.homMk
      (pullback.lift q (𝟙 X') (by
        change q ≫ 𝟙 _ = 𝟙 _ ≫ q
        rw [Category.comp_id, Category.id_comp])) (pullback.lift_snd _ _ _)
  let c := MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
    (Q := ⊤) q p g' hq.symm
  let e := (upperStarComp (ModuleCat.{u + 1} Λ) q p g' hq.symm).app F
  let tH := Sheaf.ΓNatIsoSheafSections
    (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
        (pullback f (Scheme.strictLocalizationToBase s)))
      (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)
  let tK := Sheaf.ΓNatIsoSheafSections X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
      (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)
  have ht := terminal_pullback_formula Λ q H θ
  change globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫ tK.hom.app K =
    tH.hom.app H ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app H).hom.app _ ≫
      K.obj.map θ.op at ht
  have ht' : globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H =
      tH.hom.app H ≫
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app H).hom.app _ ≫
        K.obj.map θ.op ≫ tK.inv.app K := by
    apply (cancel_mono (tK.hom.app K)).mp
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact ht
  have he := tK.inv.naturality e.inv
  change e.inv.hom.app (op (Scheme.Etale.mk (𝟙 X'))) ≫ tK.inv.app G =
    tK.inv.app K ≫ (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map e.inv at he
  dsimp only [qcqsStrictLocalSectionRestriction]
  change (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
    (op U) ≫ H.obj.map δ.op ≫ tH.inv.app H) ≫
    globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map e.inv = _
  rw [ht']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← he]
  have hn := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app H).hom.naturality
    δ.op
  change H.obj.map δ.op ≫ _ = _ ≫ K.obj.map (q.Etale.map δ).op at hn
  rw [reassoc_of% hn]
  have hn' := e.inv.hom.naturality (θ ≫ q.Etale.map δ).op
  change K.obj.map (θ ≫ q.Etale.map δ).op ≫ _ =
    e.inv.hom.app (op (q.Etale.obj (p.Etale.obj U))) ≫
      G.obj.map (θ ≫ q.Etale.map δ).op at hn'
  rw [← K.obj.map_comp_assoc, ← op_comp, reassoc_of% hn']
  have hu := congrArg (fun a ↦ a.hom.app (op U))
    (pre_composite_unit Λ q p g' hq.symm F)
  change _ ≫ _ ≫ e.inv.hom.app (op (q.Etale.obj (p.Etale.obj U))) =
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app F).hom.app
      (op U) ≫ G.obj.map (c.inv.app U).op at hu
  erw [reassoc_of% hu]
  rw [← G.obj.map_comp_assoc, ← op_comp]
  have hlift : θ ≫ q.Etale.map δ ≫ c.inv.app U =
      geometricFibreSectionLift sq V
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change θ.left ≫ (q.Etale.map δ).left ≫ (c.inv.app U).left ≫
        pullback.fst U.hom g' = _
      simp only [Functor.id_obj, Functor.const_obj_obj, Scheme.Hom.Etale,
        Functor.comp_obj, θ,
        MorphismProperty.Over.homMk_hom, Over.homMk_left, MorphismProperty.Over.pullback_map_left,
        c, MorphismProperty.Over.pullbackComp_inv_app_left,
        Category.assoc,
        geometricFibreSectionLift, MorphismProperty.Over.homMk_hom, Over.homMk_left,
        pullback.lift_fst]
      apply pullback.hom_ext
      · simp only [Category.comp_id, Category.assoc,
          pullbackLeftPullbackSndIso_hom_fst_assoc]
        erw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]
        simp only [Category.assoc]
        erw [pullback.lift_fst_assoc]
        simp only [δ, qcqsStrictLocalNeighbourhoodSection,
          MorphismProperty.Over.homMk_hom, Over.homMk_left]
        erw [pullback.lift_fst_assoc, pullback.lift_fst]
        simp only [Scheme.strictHenselizationBaseChangeMap, Category.assoc]
        erw [pullback.lift_fst]
        simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst]
        rw [hqt]
        simp only [Category.assoc]
        rw [← Scheme.isoSpec_Spec_inv, hpoint j]
      · simp only [Category.comp_id, Category.assoc,
          pullbackLeftPullbackSndIso_hom_fst_assoc]
        erw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]
        simp only [Category.assoc]
        erw [pullback.lift_fst_assoc]
        simp only [δ, qcqsStrictLocalNeighbourhoodSection,
          MorphismProperty.Over.homMk_hom, Over.homMk_left]
        erw [pullback.lift_fst_assoc, pullback.lift_snd]
        simp only [Scheme.strictHenselizationBaseChangeMap, Category.assoc]
        erw [pullback.lift_snd]
        simp only [pullbackSymmetry_hom_comp_snd]
        exact hq
    · exact (θ ≫ q.Etale.map δ ≫ c.inv.app U).w.trans
        (geometricFibreSectionLift sq V
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j).2).w.symm
  erw [Category.assoc θ (q.Etale.map δ) (c.inv.app U), hlift]
  rfl


end AlgebraicGeometry.Etale
