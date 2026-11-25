/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleRestrictionPullbackUnit

/-! # Evaluation on an étale object and global sections

Source: Stacks Project, Tag 03S2.
(blueprint: lem-weil-pbc-etale-object-sections-base-change)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural evaluation/global-sections comparison for an étale object.
Source: Stacks Project, Tag 03S2.
(blueprint: lem-weil-pbc-etale-object-sections-base-change) -/
noncomputable def etaleObjectSectionsIso {X : Scheme.{u}} (V : X.Etale) :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V) ≅
      upperStar AddCommGrpCat.{u + 1} V.hom ⋙
        Sheaf.Γ V.left.smallEtaleTopology AddCommGrpCat.{u + 1} := by
  let A := AddCommGrpCat.{u + 1}
  let w : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.hom)).obj w ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [w])
  exact (sheafSections X.smallEtaleTopology A).mapIso eW.op ≪≫
    Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction A V.hom inferInstance).symm
      ((sheafSections V.left.smallEtaleTopology A).obj (op w)) ≪≫
    Functor.isoWhiskerLeft (upperStar A V.hom)
      (Sheaf.ΓNatIsoSheafSections V.left.smallEtaleTopology A
        (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left)).symm

private lemma terminalEvaluation_eq_res {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  dsimp
  erw [Adjunction.homEquiv_counit]
  erw [Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Étale evaluation is compatible with the unit for an arbitrary base change.
Source: Stacks Project, Tags 03CF, 03EF and 03S2.
(blueprint: lem-weil-pbc-etale-object-sections-base-change)

Proof: Write p = Vf.hom and q = Vg.hom. The lift i = pullback.lift m q hm'
identifies Vg with Vf ×_Y X: its inverse is obtained by composing the projection to Vf
with Vf's projection to W and pairing that with the projection to X; the two identities
follow by pullback extensionality, hm, hm' and g = h ≫ f. Thus i is an isomorphism.
Apply etale_restriction_pullback_unit to (h,p,m,q) and i. In that equality the
restriction comparisons rhoH and rho(h^*H) are invertible. Move them to the other
sides and compose with global-sections/terminal-evaluation comparisons. Their inverses,
together with the identity-object isomorphisms eW and eW', are precisely the two
etaleObjectSectionsIso components in this statement. The map theta is the inverse of
the terminal-object pullback isomorphism used in globalSectionsUpperStarMap: both maps
have projections m and the identity, so pullback extensionality identifies them.
The composite of the h-unit on Vf with restriction along i is the W-component of the
f-pushforward of that unit followed by lowerStarComp; this follows from its definition
by the canonical pullback-pasting isomorphism and uniqueness of the two projections.
Finally, naturality of terminal evaluation moves the comparison
(upperStarComp m p)^{-1} followed by upperStarComp q h past evaluation, giving exactly
the final Γ-map displayed here. No property of H or of h is used.
-/
theorem etaleObjectSections_baseChange {R X Y : Scheme.{u}} (W : R.Etale)
    (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R) (w : g = h ≫ f)
    (m : pullback W.hom g ⟶ pullback W.hom f)
    (hm : m ≫ pullback.fst W.hom f = pullback.fst W.hom g)
    (hm' : m ≫ pullback.snd W.hom f = pullback.snd W.hom g ≫ h)
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let Vf := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
    let Vg := (MorphismProperty.Over.pullback @Etale ⊤ g).obj W
    (((lowerStar A f).map ((upperStarLowerStarAdjunction A h).unit.app H) ≫
        (lowerStarComp A h f g w).hom.app _).hom.app (op W)) ≫
        (etaleObjectSectionsIso Vg).hom.app ((upperStar A h).obj H) =
      (etaleObjectSectionsIso Vf).hom.app H ≫
        globalSectionsUpperStarMap A m ((upperStar A Vf.hom).obj H) ≫
        (Sheaf.Γ Vg.left.smallEtaleTopology A).map
          ((upperStarComp A m Vf.hom (m ≫ Vf.hom) rfl).inv.app H ≫
            (upperStarComp A Vg.hom h (m ≫ Vf.hom) hm').hom.app H)  := by
  let A := AddCommGrpCat.{u + 1}
  let Vf := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let Vg := (MorphismProperty.Over.pullback @Etale ⊤ g).obj W
  let i := pullback.lift m Vg.hom hm'
  let j : pullback Vf.hom h ⟶ Vg.left :=
    pullback.lift (pullback.fst Vf.hom h ≫ pullback.fst W.hom f)
      (pullback.snd Vf.hom h) (by
        simp only [w, Category.assoc, pullback.condition]
        exact (pullback.condition_assoc (f := Vf.hom) (g := h) f))
  have hi : IsIso i := by
    refine ⟨⟨j, ?_, ?_⟩⟩
    · apply pullback.hom_ext <;> simp [i, j, Vf, Vg, hm]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [i, j, Vf, Vg, hm]
        · simp [i, j, Vf, Vg, hm', pullback.condition]
      · simp [i, j, Vf, Vg]
  let _ : IsIso i := hi
  obtain ⟨hp', hu⟩ := etale_restriction_pullback_unit h Vf.hom m Vg.hom hm' i
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have huH := hu H
  dsimp only at huH
  let F := (upperStar A Vf.hom).obj H
  let G := (upperStar A h).obj H
  let K := (upperStar A m).obj F
  let k := (upperStarComp A m Vf.hom (m ≫ Vf.hom) rfl).inv.app H ≫
    (upperStarComp A Vg.hom h (m ≫ Vf.hom) hm').hom.app H
  let wF : Vf.left.Etale := Scheme.Etale.mk (𝟙 Vf.left)
  let wG : Vg.left.Etale := Scheme.Etale.mk (𝟙 Vg.left)
  let eF : (MorphismProperty.Over.map ⊤ (inferInstance : Etale Vf.hom)).obj wF ≅ Vf :=
    MorphismProperty.Over.isoMk (Iso.refl Vf.left) (by simp [wF])
  let eG : (MorphismProperty.Over.map ⊤ hp').obj wG ≅ Vg :=
    MorphismProperty.Over.isoMk (Iso.refl Vg.left) (by simp [wG])
  let rF := (upperStarIsoLocalizationRestriction A Vf.hom inferInstance).app H
  let rG := (upperStarIsoLocalizationRestriction A Vg.hom hp').app G
  let tF := Sheaf.ΓNatIsoSheafSections Vf.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) Vf.left)
  let tG := Sheaf.ΓNatIsoSheafSections Vg.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) Vg.left)
  let theta : wG ⟶ (MorphismProperty.Over.pullback @Etale ⊤ m).obj wF :=
    MorphismProperty.Over.homMk (pullback.lift m (𝟙 Vg.left)
      ((Category.comp_id m).trans (Category.id_comp m).symm)) (by simp [wG])
  let b : Vg ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).obj Vf :=
    MorphismProperty.Over.homMk i (pullback.lift_snd _ _ _)
  have hbSite : (MorphismProperty.Over.pullbackComp
      (P := @Etale) (Q := ⊤) h f g w).hom.app W = b := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [b, i, Vf, Vg, hm]
      · simp [b, i, Vf, Vg, hm', pullback.condition]
    · simp [b, i, Vf, Vg]
  have hb : ((lowerStarComp A h f g w).hom.app G).hom.app (op W) =
      G.obj.map b.op := by
    simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
      Iso.symm_inv, hbSite]
  have ht : globalSectionsUpperStarMap A m F ≫ tG.hom.app K =
      tF.hom.app F ≫ ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
        K.obj.map theta.op := by
    let a : wF ⟶ ⊤_ Vf.left.Etale := terminal.from _
    let c : wG ⟶ ⊤_ Vg.left.Etale := terminal.from _
    have hG : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
        K.ΓRes (op wG) = K.obj.map c.op := by
      erw [← Sheaf.ΓRes_map K c.op, ← terminalEvaluation_eq_res _ _ terminalIsTerminal K]
      simp only [Iso.inv_hom_id_app_assoc]
    have hterm : c ≫ (PreservesTerminal.iso m.Etale).inv =
        theta ≫ (MorphismProperty.Over.pullback @Etale ⊤ m).map a := by
      exact (terminalIsTerminal.isTerminalObj m.Etale).hom_ext _ _
    simp only [globalSectionsUpperStarMap, tF, tG, terminalEvaluation_eq_res,
      Category.assoc]
    change F.ΓRes (op (⊤_ Vf.left.Etale)) ≫
      ((upperStarLowerStarAdjunction A m).unit.app F).hom.app _ ≫
      K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
      K.ΓRes (op wG) = _
    erw [hG]
    have hmaps : K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫ K.obj.map c.op =
        K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ m).map a).op ≫
          K.obj.map theta.op := by
      rw [← Functor.map_comp, ← op_comp, hterm, op_comp, Functor.map_comp]
    erw [hmaps]
    have hn := ((upperStarLowerStarAdjunction A m).unit.app F).hom.naturality a.op
    change F.obj.map a.op ≫ _ = _ ≫
      K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ m).map a).op at hn
    erw [← reassoc_of% hn]
    erw [← Sheaf.ΓRes_map F a.op]
    rfl
  have hEF : (etaleObjectSectionsIso Vf).hom.app H =
      H.obj.map eF.hom.op ≫ rF.inv.hom.app (op wF) ≫ tF.inv.app F := by rfl
  have hEG : (etaleObjectSectionsIso Vg).hom.app G =
      G.obj.map eG.hom.op ≫ rG.inv.hom.app (op wG) ≫
        tG.inv.app ((upperStar A Vg.hom).obj G) := by rfl
  change ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
      K.obj.map theta.op ≫ k.hom.app (op wG) ≫ rG.hom.hom.app (op wG) ≫
        G.obj.map eG.inv.op =
    rF.hom.hom.app (op wF) ≫ H.obj.map eF.inv.op ≫
      ((upperStarLowerStarAdjunction A h).unit.app H).hom.app (op Vf) ≫
        G.obj.map b.op at huH
  have hz := congrArg (fun a ↦ H.obj.map eF.hom.op ≫ rF.inv.hom.app (op wF) ≫ a ≫
    G.obj.map eG.hom.op ≫ rG.inv.hom.app (op wG) ≫
      tG.inv.app ((upperStar A Vg.hom).obj G)) huH
  have hrG : rG.hom.hom.app (op wG) ≫ rG.inv.hom.app (op wG) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      Iso.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  have hrF : rF.inv.hom.app (op wF) ≫ rF.hom.hom.app (op wF) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      Iso.inv_hom_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  have heG : G.obj.map eG.inv.op ≫ G.obj.map eG.hom.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id]
    exact G.obj.map_id _
  have heF : H.obj.map eF.hom.op ≫ H.obj.map eF.inv.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id]
    exact H.obj.map_id _
  simp only [Category.assoc] at hz
  rw [reassoc_of% heG, reassoc_of% hrG, reassoc_of% hrF, reassoc_of% heF] at hz
  change (((lowerStar A f).map ((upperStarLowerStarAdjunction A h).unit.app H) ≫
    (lowerStarComp A h f g w).hom.app G).hom.app (op W)) ≫
    (etaleObjectSectionsIso Vg).hom.app G =
      (etaleObjectSectionsIso Vf).hom.app H ≫ globalSectionsUpperStarMap A m F ≫
        (Sheaf.Γ Vg.left.smallEtaleTopology A).map k
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStar_map_hom_app, hb]
  rw [hEF, hEG]
  have hn := tG.inv.naturality k
  change k.hom.app (op wG) ≫ tG.inv.app _ = tG.inv.app K ≫
    (Sheaf.Γ Vg.left.smallEtaleTopology A).map k at hn
  have ht' : globalSectionsUpperStarMap A m F =
      tF.hom.app F ≫ ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
        K.obj.map theta.op ≫ tG.inv.app K := by
    apply (cancel_mono (tG.hom.app K)).1
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact ht
  rw [ht']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← hn]
  exact hz.symm

end AlgebraicGeometry.Etale
