/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.ConstructibleSheaf.Defs
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import all WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Pullback of the constant scalar coefficient -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint upperStar

private theorem composite_adj_hom
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B} {H : C ⥤ A}
    (b : F ⊣ G) (a : L ⊣ R) (e : R ⋙ G ≅ H)
    (x : A) (y : C) (h : L.obj (F.obj x) ⟶ y) :
    ((b.comp a).ofNatIsoRight e).homEquiv x y h =
      (b.unit.app x ≫ G.map (a.unit.app (F.obj x) ≫ R.map h)) ≫ e.hom.app y := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  rfl

private theorem restriction_preservesSheafification
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u}) :
    X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} φ) :=
  Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)

attribute [local instance] restriction_preservesSheafification

private theorem constantRestriction_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u}) (M : ModuleCat.{u + 1} B) :
    (ModuleCat.restrictScalars.{u + 1} φ).map
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} B)
          terminalIsTerminal).unit.app M) ≫
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ X.Etale))).map
        ((constantCommuteCompose X.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} φ)).hom.app M) =
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).unit.app ((ModuleCat.restrictScalars.{u + 1} φ).obj M) := by
  have h : Functor.whiskerRight
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M))
        (ModuleCat.restrictScalars.{u + 1} φ) ≫
      ((constantCommuteCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} φ)).hom.app M).hom =
    toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj ((ModuleCat.restrictScalars.{u + 1} φ).obj M)) := by
    rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
      sheafComposeIso_inv_fac, ← toSheafify_naturality]
    ext U x
    rfl
  simpa only [constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, Functor.constCompEvaluationObj_hom_app,
    Category.id_comp, Functor.comp_obj, Functor.comp_map,
    sheafificationAdjunction_unit_app, sheafSections, Functor.flip_obj_map,
    Functor.comp_map, evaluation, Functor.flip_obj_obj,
    sheafToPresheaf, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    Functor.id_obj, Functor.const_obj_obj,
    Functor.whiskerRight_app, NatTrans.comp_app] using congr_app h (op (⊤_ X.Etale))

/-- Scalar restriction and ordinary constant inverse image commute.
Source: Stacks Tags 03EK and 07A6 (blueprint: lem-pur-etale-ordinary-constant-restriction).
Proof: transpose under inverse image and constant sheaf. The restriction square
has identity direct-image mate; naturality and the constant-adjunction units
then identify both transposes. -/
theorem etaleOrdinaryConstantRestrictionPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ModuleCat.{u + 1} B) :
    (upperStar (ModuleCat.{u + 1} A) f).map
        ((@constantCommuteCompose _ inferInstance Y.smallEtaleTopology
          (ModuleCat.{u + 1} B) inferInstance inferInstance
          (ModuleCat.{u + 1} A) inferInstance (ModuleCat.restrictScalars.{u + 1} φ)
          inferInstance
          (Sheaf.preservesSheafification_of_adjunction Y.smallEtaleTopology
            (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ))
          inferInstance).hom.app M) ≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
        ((ModuleCat.restrictScalars.{u + 1} φ).obj M) =
    (upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)).obj M) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} B) f).hom.app M) ≫
      (@constantCommuteCompose _ inferInstance X.smallEtaleTopology
          (ModuleCat.{u + 1} B) inferInstance inferInstance
          (ModuleCat.{u + 1} A) inferInstance (ModuleCat.restrictScalars.{u + 1} φ)
          inferInstance
          (Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
            (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ))
          inferInstance).hom.app M := by
  let cY := (constantCommuteCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} φ)).app M
  let cX := (constantCommuteCompose X.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} φ)).app M
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let GY := (sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (⊤_ Y.Etale))
  let GX := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (⊤_ X.Etale))
  let e : (lowerStar (ModuleCat.{u + 1} A) f) ⋙ GY ≅ GX :=
    lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) f
  have hu := unit_mateEquiv b a
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)).obj M)
  change _ ≫ (mateEquiv b a (TwoSquare.mk _ _ _ _
    (upperStarRestrictScalarsIsoSheaf φ f).hom)).app _ = _ at hu
  dsimp only [a, b] at hu
  rw [underived_mate] at hu
  dsimp only [lowerStarRestrictScalarsIso, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Functor.comp_obj, Functor.id_obj, TwoSquare.mk] at hu
  change (upperStar (ModuleCat.{u + 1} A) f).map cY.hom ≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
        ((ModuleCat.restrictScalars.{u + 1} φ).obj M) =
    (upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)).obj M) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} B) f).hom.app M) ≫
      cX.hom
  apply (cancel_epi ((upperStar (ModuleCat.{u + 1} A) f).map cY.inv)).1
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply ((((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).comp a).ofNatIsoRight e).homEquiv _ _).injective
  rw [composite_adj_hom, composite_adj_hom]
  change
    ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).unit.app ((ModuleCat.restrictScalars.{u + 1} φ).obj M) ≫
      GY.map (a.unit.app _ ≫ (lowerStar (ModuleCat.{u + 1} A) f).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          ((ModuleCat.restrictScalars.{u + 1} φ).obj M)))) ≫ e.hom.app _ =
    ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).unit.app ((ModuleCat.restrictScalars.{u + 1} φ).obj M) ≫
      GY.map (a.unit.app _ ≫ (lowerStar (ModuleCat.{u + 1} A) f).map
        ((upperStar (ModuleCat.{u + 1} A) f).map cY.inv ≫
          (upperStarRestrictScalarsIsoSheaf φ f).hom.app
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)).obj M) ≫
          (Sheaf.restrictScalars X.smallEtaleTopology φ).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} B) f).hom.app M) ≫
          cX.hom))) ≫ e.hom.app _
  simp only [Functor.map_comp, Category.assoc]
  simp only [← GY.map_comp_assoc]
  erw [a.unit_naturality_assoc, ← reassoc_of% hu]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e.hom.naturality cX.hom
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  have hcY := constantRestriction_unit φ Y M
  have hcX := constantRestriction_unit φ X M
  have hA := Scheme.unit_app_upperStarConstantSheafIso (ModuleCat.{u + 1} A) f
    ((ModuleCat.restrictScalars.{u + 1} φ).obj M)
  have hB := congrArg (ModuleCat.restrictScalars.{u + 1} φ).map
    (Scheme.unit_app_upperStarConstantSheafIso (ModuleCat.{u + 1} B) f M)
  simp only [Functor.map_comp, Category.assoc] at hB hA
  erw [hA]
  change _ =
    (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).unit.app ((ModuleCat.restrictScalars.{u + 1} φ).obj M) ≫
      GY.map cY.inv ≫
      (ModuleCat.restrictScalars.{u + 1} φ).map
        (((sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
          (op (⊤_ Y.Etale))).map
          (b.unit.app ((constantSheaf Y.smallEtaleTopology
            (ModuleCat.{u + 1} B)).obj M))) ≫
      (ModuleCat.restrictScalars.{u + 1} φ).map
        (((sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
          (op (⊤_ Y.Etale))).map
          ((lowerStar (ModuleCat.{u + 1} B) f).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} B) f).hom.app M))) ≫
      (ModuleCat.restrictScalars.{u + 1} φ).map
        ((lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} B) f).hom.app _) ≫
      GX.map cX.hom
  erw [← hcY]
  simp only [Category.assoc]
  erw [← GY.map_comp_assoc, Iso.hom_inv_id cY, GY.map_id, Category.id_comp]
  erw [reassoc_of% hB]
  exact hcX.symm

end AlgebraicGeometry.Etale
