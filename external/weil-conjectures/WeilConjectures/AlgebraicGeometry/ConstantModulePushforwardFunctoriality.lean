/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Functorial maps between direct images of constant modules

Source: Stacks Project, Tag 09Z1, canonical transition maps.
(blueprint: lem-weil-pbc-constant-module-pushforward-functoriality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Pull back constant-module sections along a morphism over the base, using the
inverse-image adjunction and its canonical constant-sheaf comparison. -/
noncomputable def constantModulePushforwardMap
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
    (g : Y₂ ⟶ Y₁) (h : g ≫ f₁ = f₂) :
    (lowerStar (ModuleCat.{u + 1} Λ) f₁).obj
        ((constantSheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) f₂).obj
        ((constantSheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (lowerStar (ModuleCat.{u + 1} Λ) f₁).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)) ≫
    (lowerStarComp (ModuleCat.{u + 1} Λ) g f₁ f₂ h.symm).hom.app _

/-- The adjoint of the constant-sheaf pullback comparison. -/
private noncomputable def constantModuleTransition
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) g).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
    (lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)

set_option backward.isDefEq.respectTransparency false in
/-- The transition preserves the sheafification generator at the terminal object.
This is the unit equation for uniqueness of left adjoints, followed by naturality. -/
private lemma constantModuleTransition_terminal
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
        (Opposite.op (⊤_ Y.Etale)) ≫
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)).hom).app
            (Opposite.op (⊤_ Y.Etale)) ≫
      ((lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.app _) =
    (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (Opposite.op (⊤_ Z.Etale)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g))
    (constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal) M
  change
    ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
        (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _).hom.app
        (Opposite.op (⊤_ Y.Etale))) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.app _ ≫
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M).hom.app
        (Opposite.op (⊤_ Z.Etale)) = _ at h
  have hn := (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.naturality
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  change
    ((lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)).hom.app
          (Opposite.op (⊤_ Y.Etale)) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.app _ =
    (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).hom.app _ ≫
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M).hom.app
        (Opposite.op (⊤_ Z.Etale)) at hn
  exact (congrArg (fun k ↦
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
      (Opposite.op (⊤_ Y.Etale)) ≫
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _).hom.app
      (Opposite.op (⊤_ Y.Etale)) ≫ k) hn).trans (by
      simpa only [Category.assoc, constantSheafAdj, Adjunction.comp_unit_app,
        constantPresheafAdj_unit_app, Functor.constCompEvaluationObj_hom_app,
        Category.id_comp, sheafificationAdjunction_unit_app, Functor.comp_obj,
        evaluation, constantSheaf, sheafSections, Functor.flip, sheafToPresheaf] using h)

set_option backward.isDefEq.respectTransparency false in
/-- The transition preserves all constant-presheaf generators.
Transport the terminal-object equation along the unique map to the terminal object. -/
private lemma constantModuleTransition_generators
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) (U : Y.Etaleᵒᵖ) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app U ≫
      (constantModuleTransition Λ M g).hom.app U =
    (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (g.Etale.op.obj U) := by
  let CY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let CZ := (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let t : CY ⟶ (lowerStar (ModuleCat.{u + 1} Λ) g).obj CZ :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)
  let eY := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  let eZ := toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)
  let a := (terminalIsTerminal.from U.unop).op
  let i := PreservesTerminal.iso g.Etale
  have ht := constantModuleTransition_terminal Λ M g
  change eY.app (Opposite.op (⊤_ Y.Etale)) ≫ t.hom.app _ ≫
    CZ.obj.map i.inv.op = eZ.app (Opposite.op (⊤_ Z.Etale)) at ht
  have ht' := congrArg (fun k ↦ k ≫ CZ.obj.map i.hom.op) ht
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp,
    Iso.hom_inv_id, op_id] at ht'
  change eY.app (Opposite.op (⊤_ Y.Etale)) ≫
    t.hom.app (Opposite.op (⊤_ Y.Etale)) ≫ CZ.obj.map (𝟙 _) = _ at ht'
  rw [CZ.obj.map_id] at ht'
  have ht'' : eY.app (Opposite.op (⊤_ Y.Etale)) ≫ t.hom.app _ =
      eZ.app (Opposite.op (⊤_ Z.Etale)) ≫ CZ.obj.map i.hom.op := by
    exact (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans ht')
  have hY := eY.naturality a
  have hZ := eZ.naturality ((terminalIsTerminal.from (g.Etale.obj U.unop)).op)
  dsimp only [Functor.const_obj_map, Functor.const_obj_obj] at hY hZ
  simp only [Category.id_comp] at hY hZ
  have hn := t.hom.naturality a
  dsimp only [CY, CZ, constantSheaf, Functor.comp_obj] at hn ⊢
  change eY.app U ≫ t.hom.app U = eZ.app (g.Etale.op.obj U)
  rw [hY, Category.assoc, hn, ← Category.assoc, ht'']
  change eZ.app (Opposite.op (⊤_ Z.Etale)) ≫
    CZ.obj.map i.hom.op ≫ CZ.obj.map (g.Etale.map a.unop).op = _
  dsimp only [CZ, constantSheaf, Functor.comp_obj] at *
  rw [← Functor.map_comp, ← op_comp]
  have he : g.Etale.map a.unop ≫ i.hom =
      terminalIsTerminal.from (g.Etale.obj U.unop) := terminalIsTerminal.hom_ext _ _
  rw [he]
  exact hZ.symm

set_option backward.isDefEq.respectTransparency false in
/-- Identity coherence, checked on generators using sheafification uniqueness. -/
private lemma constantModuleTransition_id
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) (Y : Scheme.{u}) :
    constantModuleTransition Λ M (𝟙 Y) =
      (lowerStarId (ModuleCat.{u + 1} Λ) Y).inv.app _ := by
  apply (cancel_mono ((lowerStarId (ModuleCat.{u + 1} Λ) Y).hom.app _)).1
  dsimp only [constantSheaf, Functor.comp_obj]
  rw [Iso.inv_hom_id_app]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((constantSheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).obj M).property
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, NatTrans.id_app]
  rw [← Category.assoc, constantModuleTransition_generators Λ M (𝟙 Y) U]
  simp only [lowerStarId, GrothendieckTopology.lowerStarId,
    Functor.sheafPushforwardContinuousId'_hom_app_hom_app]
  have hn := (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).naturality
    ((MorphismProperty.Over.pullbackId @Etale ⊤ Y).inv.app U.unop).op
  simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp,
    Category.comp_id, Functor.id_obj, Scheme.Hom.Etale, Functor.op_obj,
    constantSheaf, Functor.comp_obj, Opposite.op_unop, sheafify] using hn.symm

set_option backward.isDefEq.respectTransparency false in
/-- Composition coherence, checked on generators using the pullback pasting comparison. -/
private lemma constantModuleTransition_comp
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Y Z W : Scheme.{u}} (g : Z ⟶ Y) (g' : W ⟶ Z) :
    constantModuleTransition Λ M (g' ≫ g) =
      constantModuleTransition Λ M g ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).map (constantModuleTransition Λ M g') ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) g' g).hom.app _ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((lowerStar (ModuleCat.{u + 1} Λ) (g' ≫ g)).obj
    ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).property
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [constantModuleTransition_generators Λ M (g' ≫ g) U]
  rw [← Category.assoc, constantModuleTransition_generators Λ M g U]
  change _ = (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
      (g.Etale.op.obj U) ≫ (constantModuleTransition Λ M g').hom.app
      (g.Etale.op.obj U) ≫ _
  rw [← Category.assoc, constantModuleTransition_generators Λ M g' (g.Etale.op.obj U)]
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]
  have hn := (toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj M)).naturality
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g' g).hom.app U.unop).op
  simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp,
    Scheme.Hom.Etale, Functor.op_obj, constantSheaf, Functor.comp_obj, Iso.symm_inv]
    using hn

set_option backward.isDefEq.respectTransparency false in
/-- The canonical constant-module pushforward maps preserve identity and composition
contravariantly in the scheme over the base.

Source: Stacks Project, Tag 09Z1, system of sheaves and its direct-image transitions;
Tag 09Z6, finite approximation paragraph.
(blueprint: lem-weil-pbc-constant-module-pushforward-functoriality).

Proof: The map adjoint to the canonical pullback comparison sends a constant section
with value m to the constant section with value m. On an etale object of the base,
its direct image is restriction along the induced map of fibre products. Restriction
along the identity is the identity; restriction along a composite is the composite
of restrictions in reverse order. These equalities hold on constant presheaves and
extend uniquely to their sheafifications. The inverse-image adjunction identifies
these restrictions with the displayed maps. The lowerStar composition comparisons
are precisely the fibre-product pasting comparisons, so these sectionwise identities
prove both asserted equalities. This applies also to zero modules and empty schemes. -/
theorem constantModulePushforwardMap_id_comp
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) :
    (∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
      constantModulePushforwardMap Λ M f f (𝟙 Y) (Category.id_comp f) = 𝟙 _) ∧
    (∀ {X Y₁ Y₂ Y₃ : Scheme.{u}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) (f₃ : Y₃ ⟶ X)
      (g : Y₂ ⟶ Y₁) (g' : Y₃ ⟶ Y₂) (h : g ≫ f₁ = f₂) (h' : g' ≫ f₂ = f₃),
      constantModulePushforwardMap Λ M f₁ f₃ (g' ≫ g)
          (by rw [Category.assoc, h, h']) =
        constantModulePushforwardMap Λ M f₁ f₂ g h ≫
          constantModulePushforwardMap Λ M f₂ f₃ g' h') := by
  constructor
  · intro X Y f
    change (lowerStar (ModuleCat.{u + 1} Λ) f).map
        (constantModuleTransition Λ M (𝟙 Y)) ≫ _ = _
    rw [constantModuleTransition_id, lowerStarComp_id_left]
    simp [← Functor.map_comp, constantSheaf]
  · intro X Y₁ Y₂ Y₃ f₁ f₂ f₃ g g' h h'
    have key := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ)
      g' g f₁ (g' ≫ g) f₂ f₃ rfl h.symm
      (by rw [Category.assoc, h, h']))
      ((constantSheaf Y₃.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
    change (lowerStar (ModuleCat.{u + 1} Λ) f₁).map
        (constantModuleTransition Λ M (g' ≫ g)) ≫ _ =
      ((lowerStar (ModuleCat.{u + 1} Λ) f₁).map (constantModuleTransition Λ M g) ≫ _) ≫
        ((lowerStar (ModuleCat.{u + 1} Λ) f₂).map (constantModuleTransition Λ M g') ≫ _)
    rw [constantModuleTransition_comp]
    simp only [Functor.map_comp, Category.assoc, key]
    rw [← NatTrans.naturality_assoc]
    rfl

end AlgebraicGeometry.Etale
