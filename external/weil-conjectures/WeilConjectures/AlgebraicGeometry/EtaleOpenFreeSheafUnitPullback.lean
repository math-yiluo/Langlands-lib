/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenFreeSheafPullback
import WeilConjectures.AlgebraicGeometry.ConstantSectionAdjunctPullback
import WeilConjectures.AlgebraicGeometry.OpenRestrictionPullbackUnit
import all WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalWholeToOpen

/-! # Pullback of the open identity generator
Source: Stacks Project, Tags 03F3, 01F8 and 01FB.
(blueprint: lem-weil-pbc-etale-open-free-sheaf-unit-pullback)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private lemma openGenerator_sections {X : Scheme.{u}} (U : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι) ⟶ F) :
    let b := Scheme.Etale.mk (𝟙 U.toScheme)
    let v := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj b
    let t : v ⟶ Scheme.Etale.mk U.ι :=
      MorphismProperty.Over.homMk (𝟙 U.toScheme) (by rfl)
    ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι inferInstance).hom.app
      F).hom.app (op b)
        (((upperStar AddCommGrpCat.{u + 1} U.ι).map f).hom.app (op b)
          (etaleOpenFreeSheafSection U)) =
      F.obj.map t.op
        (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk U.ι) F f) := by
  dsimp only
  let b := Scheme.Etale.mk (𝟙 U.toScheme)
  let ρ := upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι inferInstance
  have hn := congrArg (fun q ↦ q.hom.app (op b)) (ρ.hom.naturality f)
  change _ ≫ _ = _ ≫ _ at hn
  rw [← ConcreteCategory.comp_apply, hn, ConcreteCategory.comp_apply]
  dsimp only [etaleOpenFreeSheafSection]
  change (f.hom.app _)
    (((ρ.hom.app _).hom.app (op b)) (((ρ.inv.app _).hom.app (op b)) _)) = _
  have hi := congrArg (fun q ↦ q.hom.app (op b))
    (ρ.inv_hom_id_app ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)))
  change _ ≫ _ = 𝟙 _ at hi
  rw [← ConcreteCategory.comp_apply, hi]
  exact sectionsEquiv_generator _ F f _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma openGenerator_identity {X : Scheme.{u}} (U : X.Opens) :
    let A := (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)
    let b := Scheme.Etale.mk (𝟙 U.toScheme)
    let v := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj b
    let q : Scheme.Etale.mk U.ι ⟶ v :=
      MorphismProperty.Over.homMk (𝟙 U.toScheme)
        ((Category.id_comp _).trans (Category.id_comp _))
    A.obj.map q.op
      (((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
        inferInstance).hom.app A).hom.app (op b) (etaleOpenFreeSheafSection U)) =
      EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk U.ι) A
        (𝟙 A) := by
  dsimp only
  let A := (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)
  let b := Scheme.Etale.mk (𝟙 U.toScheme)
  let v := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj b
  let e : v ≅ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
  have h := openGenerator_sections U A (𝟙 A)
  dsimp only at h
  rw [(upperStar AddCommGrpCat.{u + 1} U.ι).map_id] at h
  change ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
    inferInstance).hom.app A).hom.app (op b) (etaleOpenFreeSheafSection U) =
      A.obj.map e.hom.op
        (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk U.ι) A
          (𝟙 A)) at h
  change A.obj.map e.inv.op
    (((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
      inferInstance).hom.app A).hom.app (op b) (etaleOpenFreeSheafSection U)) = _
  rw [h]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    e.inv_hom_id, op_id, CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
/-- The degree-zero identity generator commutes with pullback.
Source: Stacks Project, Tag 03F3 (localization), Tags 01F8/01FB (functoriality).
(blueprint: lem-weil-pbc-etale-open-free-sheaf-unit-pullback)

Proof: Apply the constant-sheaf adjunction at the terminal object of the inverse-image
open, then evaluate the homomorphism from the integers at 1. Naturality turns the left
side into the section classified by etaleOpenFreeSheafPullback, transported by the
localization comparison. By the free abelian Yoneda adjunction this is the inverse-image
unit at the identity generator, restricted along openSectionPullback. The constant-sheaf
pullback adjunct formula turns the right side into pullback of the original identity
section along morphismRestrict. The open restriction pullback unit equation identifies
these sections, including the displayed composition comparisons. The two adjunction
bijections give the morphism equality. All constructions apply also to the empty open.
-/
theorem etaleOpenFreeSheafUnit_pullback {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens) :
    etaleOpenFreeSheafUnit (g ⁻¹ᵁ W) ≫
      (upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι).map
        (etaleOpenFreeSheafPullback g W) =
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (g ∣_ W)).inv.app
        (AddCommGrpCat.of (ULift ℤ)) ≫
      (upperStar AddCommGrpCat.{u + 1} (g ∣_ W)).map (etaleOpenFreeSheafUnit W) ≫
      ((upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι
          ((g ⁻¹ᵁ W).ι ≫ g) (morphismRestrict_ι g W).symm).inv ≫
        (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g).hom).app
          ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)) := by
  let A := (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)
  let F := (upperStar AddCommGrpCat.{u + 1} g).obj A
  let b := Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme)
  let v := (MorphismProperty.Over.map ⊤ (inferInstance : Etale (g ⁻¹ᵁ W).ι)).obj b
  let e : v ≅ Scheme.Etale.mk (g ⁻¹ᵁ W).ι :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
  let ρ := upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι
    inferInstance
  let adj := constantSheafAdj (g ⁻¹ᵁ W).toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
    (show IsTerminal b from IsTerminal.ofUniqueHom
      (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
      (fun a f ↦ by
        apply MorphismProperty.Over.Hom.ext
        exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))
  -- Compare the classified sections, transported from the terminal object to the open.
  apply (adj.homEquiv _ _).injective
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  apply (((sheafSections (g ⁻¹ᵁ W).toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (op b)).mapIso (ρ.app F)).addCommGroupIsoToAddEquiv.injective
  apply (F.obj.mapIso e.op.symm).addCommGroupIsoToAddEquiv.injective
  have hz {B C : AddCommGrpCat.{u + 1}}
      (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ B) (k : B ⟶ C) :
      AddCommGrpCat.uliftZMultiplesAddEquiv C (f ≫ k) =
        k (AddCommGrpCat.uliftZMultiplesAddEquiv B f) := by rfl
  let c := ((upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι
      ((g ⁻¹ᵁ W).ι ≫ g) (morphismRestrict_ι g W).symm).inv ≫
    (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g).hom).app A
  simp only [← Category.assoc]
  change F.obj.map e.inv.op ((ρ.hom.app F).hom.app (op b)
    (AddCommGrpCat.uliftZMultiplesAddEquiv _ (adj.homEquiv _ _
      (etaleOpenFreeSheafUnit (g ⁻¹ᵁ W) ≫
        (upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι).map
          (etaleOpenFreeSheafPullback g W))))) =
    F.obj.map e.inv.op ((ρ.hom.app F).hom.app (op b)
      (AddCommGrpCat.uliftZMultiplesAddEquiv _ (adj.homEquiv _ _
        (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (g ∣_ W)).inv.app
          (AddCommGrpCat.of (ULift ℤ)) ≫
          (upperStar AddCommGrpCat.{u + 1} (g ∣_ W)).map (etaleOpenFreeSheafUnit W)) ≫ c))))
  -- The left side classifies exactly the section defining the free-sheaf pullback.
  rw [adj.homEquiv_naturality_right, hz]
  have hl : AddCommGrpCat.uliftZMultiplesAddEquiv _
      (adj.homEquiv _ _ (etaleOpenFreeSheafUnit (g ⁻¹ᵁ W))) =
        etaleOpenFreeSheafSection (g ⁻¹ᵁ W) := by
    simp only [adj, b, etaleOpenFreeSheafUnit, Equiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
  rw [hl]
  change F.obj.map e.inv.op ((ρ.hom.app F).hom.app (op b)
    (((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι).map
      (etaleOpenFreeSheafPullback g W)).hom.app (op b)
        (etaleOpenFreeSheafSection (g ⁻¹ᵁ W)))) = _
  rw [openGenerator_sections]
  change F.obj.map e.inv.op (F.obj.map e.hom.op _) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    e.inv_hom_id, op_id, CategoryTheory.Functor.map_id]
  change EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
    (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) F (etaleOpenFreeSheafPullback g W) = _
  simp only [etaleOpenFreeSheafPullback]
  erw [AddEquiv.apply_symm_apply]
  -- The right side is the restricted pullback of the original identity section.
  rw [adj.homEquiv_naturality_right, constantSection_adjunct_pullback, hz, hz]
  simp only [etaleOpenFreeSheafUnit, Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let c₀ := ((upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι).inv ≫
    (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g
      ((g ∣_ W) ≫ W.ι) (morphismRestrict_ι g W)).hom).app A
  -- Changing the common composite does not change the square comparison.
  have hc : c = c₀ := by
    have h (k : (g ⁻¹ᵁ W).toScheme ⟶ X) (h₁ : k = (g ∣_ W) ≫ W.ι)
        (h₂ : k = (g ⁻¹ᵁ W).ι ≫ g) :
        (upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι k h₁).inv ≫
          (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g k h₂).hom =
        (upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι).inv ≫
          (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g
            ((g ∣_ W) ≫ W.ι) (morphismRestrict_ι g W)).hom := by
      subst h₁
      rfl
    exact congrArg (fun q ↦ q.app A) (h _ (morphismRestrict_ι g W).symm rfl)
  rw [hc]
  -- The restriction-unit equation identifies the two computed sections.
  have hu := open_restriction_pullback_unit g W A
  have hu' := ConcreteCategory.congr_hom hu (etaleOpenFreeSheafSection W)
  simp only [ConcreteCategory.comp_apply] at hu'
  erw [openGenerator_identity W] at hu'
  convert hu'.symm using 1 <;> rfl

end AlgebraicGeometry.Etale
