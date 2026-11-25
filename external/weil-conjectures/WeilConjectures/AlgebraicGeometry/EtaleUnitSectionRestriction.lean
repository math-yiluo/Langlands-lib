/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-! # Restricting an étale section along a lift

Source: Stacks Project, Tags 03D3, 03D7 and 03Q9.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The graph of a lift of an étale object along a scheme map.
Source: Stacks Project, Tags 03D3 and 03D7.
(auxiliary; not a blueprint node). -/
noncomputable def etaleSectionGraph {X Z : Scheme.{u}} (p : Z ⟶ X)
    (U : X.Etale) (v : Z ⟶ U.left) (hv : v ≫ U.hom = p) :
    Scheme.Etale.mk (𝟙 Z) ⟶ p.Etale.obj U :=
  MorphismProperty.Over.homMk
    (pullback.lift v (𝟙 Z) (hv.trans (Category.id_comp p).symm))
    (pullback.lift_snd _ _ _)

/-- Restriction of a section along an arbitrary lift, using the inverse-image unit.
Source: Stacks Project, Tags 03D3, 03D7 and 03Q9.
(auxiliary; not a blueprint node). -/
noncomputable def unitSectionRestriction (Λ : Type (u + 1)) [CommRing Λ]
    {X Z : Scheme.{u}} (p : Z ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Etale) (v : Z ⟶ U.left) (hv : v ≫ U.hom = p) :
    F.obj.obj (op U) ⟶ (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      ((upperStar (ModuleCat.{u + 1} Λ) p).obj F) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app (op U) ≫
    ((upperStar (ModuleCat.{u + 1} Λ) p).obj F).obj.map (etaleSectionGraph p U v hv).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ Z)
        (Scheme.Etale.mk (𝟙 Z)) Over.mkIdTerminal)).inv.app _

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
/-- Unit restriction commutes with further pullback, including its composition comparison.
Source: Stacks Project, Tags 03D3 and 03D7, functoriality of inverse image.
(auxiliary; not a blueprint node).

Proof: express global pullback by terminal evaluation, its adjunction unit and the
terminal graph. Move restriction past the second unit by naturality. The composite
adjunction-unit equation identifies the successive units with the unit for the composite.
Naturality of the inverse-image composition isomorphism leaves the composite of graph
maps; its two projections identify it with the graph of the composite lift. Terminal
evaluation and its inverse cancel. No nonempty, finite or proper hypothesis is needed. -/
theorem unitSectionRestriction_comp
    (Λ : Type (u + 1)) [CommRing Λ] {X Z W : Scheme.{u}}
    (q : W ⟶ Z) (p : Z ⟶ X) (g : W ⟶ X) (hg : g = q ≫ p)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Etale) (v : Z ⟶ U.left) (hv : v ≫ U.hom = p) :
    unitSectionRestriction Λ p F U v hv ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ) p).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q p g hg).inv.app F) =
      unitSectionRestriction Λ g F U (q ≫ v)
        (by rw [Category.assoc, hv, ← hg]) := by
  classical
  let H := (upperStar (ModuleCat.{u + 1} Λ) p).obj F
  let K := (upperStar (ModuleCat.{u + 1} Λ) q).obj H
  let G := (upperStar (ModuleCat.{u + 1} Λ) g).obj F
  let δ := etaleSectionGraph p U v hv
  let θ : Scheme.Etale.mk (𝟙 W) ⟶ q.Etale.obj (Scheme.Etale.mk (𝟙 _)) :=
    MorphismProperty.Over.homMk
      (pullback.lift q (𝟙 W) (by
        change q ≫ 𝟙 _ = 𝟙 _ ≫ q
        rw [Category.comp_id, Category.id_comp])) (pullback.lift_snd _ _ _)
  let c := MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
    (Q := ⊤) q p g hg
  let e := (upperStarComp (ModuleCat.{u + 1} Λ) q p g hg).app F
  let tH := Sheaf.ΓNatIsoSheafSections
    Z.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
        Z)
      (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)
  let tK := Sheaf.ΓNatIsoSheafSections W.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ W)
      (Scheme.Etale.mk (𝟙 W)) Over.mkIdTerminal)
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
  change e.inv.hom.app (op (Scheme.Etale.mk (𝟙 W))) ≫ tK.inv.app G =
    tK.inv.app K ≫ (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map e.inv at he
  dsimp only [unitSectionRestriction]
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
    (pre_composite_unit Λ q p g hg F)
  change _ ≫ _ ≫ e.inv.hom.app (op (q.Etale.obj (p.Etale.obj U))) =
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F).hom.app
      (op U) ≫ G.obj.map (c.inv.app U).op at hu
  erw [reassoc_of% hu]
  rw [← G.obj.map_comp_assoc, ← op_comp]
  have hlift : θ ≫ q.Etale.map δ ≫ c.inv.app U =
      etaleSectionGraph g U (q ≫ v) (by rw [Category.assoc, hv, ← hg]) := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change θ.left ≫ (q.Etale.map δ).left ≫ (c.inv.app U).left ≫
          pullback.fst U.hom g = _
      simp only [Scheme.Hom.Etale, θ, δ, etaleSectionGraph,
        MorphismProperty.Over.homMk_hom,
        Over.homMk_left, MorphismProperty.Over.pullback_map_left,
        c, MorphismProperty.Over.pullbackComp_inv_app_left, Category.assoc,
        pullback.lift_fst]
      simp only [pullbackLeftPullbackSndIso_hom_fst, Category.comp_id]
      erw [pullback.lift_fst_assoc]
      simp only [Category.assoc]
      erw [pullback.lift_fst_assoc, pullback.lift_fst]
    · exact (θ ≫ q.Etale.map δ ≫ c.inv.app U).w.trans
        (etaleSectionGraph g U (q ≫ v) (by rw [Category.assoc, hv, ← hg])).w.symm
  erw [Category.assoc θ (q.Etale.map δ) (c.inv.app U), hlift]

end AlgebraicGeometry.Etale
