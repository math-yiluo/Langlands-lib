/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Restriction on resolution cohomology before the section-class map

Source: Stacks Project, Tags 01E2 and 01FB.
(blueprint: lem-weil-pbc-restricted-resolution-cohomology)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

private theorem restriction_component {Z : Scheme.{u}} (U : Z.Opens)
    (M : Z.Modules) (N : U.toScheme.Modules) (e : N ≅ (restrictFunctor U.ι).obj M) :
    Hom.app ((restrictAdjunction U.ι).unit.app M ≫ (pushforward U.ι).map e.inv) ⊤ ≫
      N.presheaf.map
        (eqToHom (by simp) : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ (⊤ : Z.Opens)).op ≫
      Hom.app e.hom ⊤ ≫ (restrictAppIso U.ι M ⊤).hom ≫
      M.presheaf.map (eqToHom U.ι_image_top.symm).op =
    M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  change Hom.app ((restrictAdjunction U.ι).unit.app M) ⊤ ≫
    Hom.app e.inv (U.ι ⁻¹ᵁ (⊤ : Z.Opens)) ≫ N.presheaf.map _ ≫
    Hom.app e.hom ⊤ ≫ (restrictAppIso U.ι M ⊤).hom ≫ M.presheaf.map _ = _
  have hn := (Hom.mapPresheaf e.inv).naturality
    (eqToHom (by simp) : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ (⊤ : Z.Opens)).op
  change (((restrictFunctor U.ι).obj M).presheaf.map _ ≫ Hom.app e.inv ⊤) =
    Hom.app e.inv (U.ι ⁻¹ᵁ (⊤ : Z.Opens)) ≫ N.presheaf.map _ at hn
  rw [← Category.assoc (Hom.app e.inv (U.ι ⁻¹ᵁ (⊤ : Z.Opens)))
    (N.presheaf.map
      (eqToHom (by simp) : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ (⊤ : Z.Opens)).op), ← hn]
  simp only [Category.assoc]
  have hcan : Hom.app e.inv ⊤ ≫ Hom.app e.hom ⊤ = 𝟙 _ :=
    ((RingedSpace.openModuleSections U.toScheme.toRingedSpace ⊤).mapIso e).inv_hom_id
  rw [← Category.assoc (Hom.app e.inv ⊤) (Hom.app e.hom ⊤), hcan, Category.id_comp]
  have hu : Hom.app ((restrictAdjunction U.ι).unit.app M) ⊤ =
      M.presheaf.map (homOfLE (U.ι.image_preimage_le ⊤)).op := rfl
  have hr : ((restrictFunctor U.ι).obj M).presheaf.map
      (eqToHom (by simp) : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ (⊤ : Z.Opens)).op =
      M.presheaf.map (U.ι.opensFunctor.map
        (eqToHom (by simp) : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ (⊤ : Z.Opens))).op := rfl
  rw [hu, hr]
  simp only [restrictAppIso, Iso.refl_hom, Category.id_comp]
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 1

/-- Cancel resolution comparisons before applying a functor to a commuting diagram. -/
private theorem iso_homology_transport
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {S K L M : C} {X Y Z T : D}
    (i : X ≅ Y) (j : Y ≅ H.obj S) (k : Z ≅ T) (l : T ≅ H.obj K)
    (a : K ≅ L) (β : S ⟶ L) (s : K ⟶ M) (r : S ⟶ M)
    (h : β ≫ a.inv ≫ s = r) :
    (i.hom ≫ j.hom ≫ H.map β ≫ inv (H.map a.hom) ≫ l.inv ≫ k.inv) ≫
      k.hom ≫ l.hom ≫ H.map s = i.hom ≫ j.hom ≫ H.map r := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have ha : inv (H.map a.hom) = H.map a.inv :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← H.map_comp, Iso.hom_inv_id, H.map_id])
  rw [ha, ← H.map_comp, ← H.map_comp, h]

/-- Restriction on module cohomology is computed by the restriction of sections of a
fixed resolution, followed by the pinned identification of the restricted resolution.
This is a statement about homology of section complexes, before the map to a homology sheaf.
Source: Stacks Project, Equation 20.7.1.1 (Tag 01E2), Remark 20.14.2 (Tag 01FB).
(blueprint: lem-weil-pbc-restricted-resolution-cohomology)

Proof: Let j be the inclusion of U. The restriction unit gives a map from I to
j_* of its restriction. Compose it with j_* of R.comparison.inv. Naturality of
the unit and R.augmentation show that this map lifts the restriction unit on F.
Restriction preserves finite limits, so its right adjoint j_* preserves injectives. Thus
j_*R is already termwise injective: use it as the comparison complex, with
lambda the identity, source resolution I and target resolution R, in the
construction of the cohomology map. The global sections comparison is restriction
along j inverse image of the top open, so it is an isomorphism. Independence of
the choices identifies this calculation with moduleCohomologyRestriction.
Cancel the target resolution comparison and the global sections comparison.
The degreewise formula R.components says that the surviving map is exactly
restriction from the top open to U, followed by R.sections.inv. Apply homology
and compose with R.sections.hom to obtain the displayed equality. The argument
uses only naturality and inverse identities and applies in degree zero, for zero
modules, and for the empty and top opens. -/
theorem restrictedResolution_cohomology {Z : Scheme.{u}} {F : Z.Modules}
    (I : InjectiveResolution F) (U : Z.Opens) (R : RestrictedResolutionSections I U)
    (p : ℕ) :
    let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
    let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
    moduleCohomologyRestriction U F p ≫
      (forget₂ _ AddCommGrpCat.{u}).map
        (R.resolution.isoRightDerivedObj
          (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p).hom ≫
      (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        R.sections.hom =
    (forget₂ _ AddCommGrpCat.{u}).map
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p).hom ≫
      (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
            PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
              ((evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map
                (homOfLE (show U ≤ ⊤ from le_top)).op))
          (ComplexShape.up ℕ)).app I.cocomplex) := by
  let P := pushforward U.ι
  have : P.PreservesInjectiveObjects :=
    Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits (restrictAdjunction U.ι)
  let B := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.resolution.cocomplex
  have hB : ∀ n : ℕ, Injective (B.X n) := fun n ↦
    P.injective_obj (R.resolution.cocomplex.X n)
  let η : I.cocomplex ⟶
      (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
    { f := fun n ↦ (restrictAdjunction U.ι).unit.app (I.cocomplex.X n)
      comm' := fun i j _ ↦ ((restrictAdjunction U.ι).unit.naturality
        (I.cocomplex.d i j)).symm }
  let β : I.cocomplex ⟶ B := η ≫
    (P.mapHomologicalComplex (ComplexShape.up ℕ)).map R.comparison.inv
  have haug : (restrictFunctor U.ι).map (I.ι.f 0) ≫ R.comparison.inv.f 0 =
      R.resolution.ι.f 0 := by
    rw [← R.augmentation, Category.assoc]
    have hc : R.comparison.hom.f 0 ≫ R.comparison.inv.f 0 = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    rw [hc, Category.comp_id]
  have hβ : I.ι.f 0 ≫ β.f 0 =
      (restrictAdjunction U.ι).unit.app F ≫ P.map (R.resolution.ι.f 0) := by
    dsimp only [β]
    rw [HomologicalComplex.comp_f]
    change I.ι.f 0 ≫ (restrictAdjunction U.ι).unit.app (I.cocomplex.X 0) ≫
      P.map (R.comparison.inv.f 0) = _
    erw [← Category.assoc, (restrictAdjunction U.ι).unit.naturality (I.ι.f 0)]
    change (restrictAdjunction U.ι).unit.app F ≫
      P.map ((restrictFunctor U.ι).map (I.ι.f 0)) ≫ P.map (R.comparison.inv.f 0) = _
    erw [← P.map_comp, haug]
  let a : ((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R.resolution.cocomplex ≅
      ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj B := by
    refine (HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (presheaf (R.resolution.cocomplex.X n)).mapIso
        (eqToIso (by simp) : op (U.ι ⁻¹ᵁ (⊤ : Z.Opens)) ≅
          op (⊤ : U.toScheme.Opens))) ?_).symm
    intro n m _
    exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (R.resolution.cocomplex.d n m)).naturality _
  let C : ModuleCohomologyFMapData U.ι F ((restrictFunctor U.ι).obj F)
      ((restrictAdjunction U.ι).unit.app F) := {
    I := R.resolution
    J := I
    K := B
    injective := hB
    lambda := 𝟙 _
    quasiIso := by infer_instance
    β := β
    compatible := by
      change I.ι.f 0 ≫ β.f 0 =
        (restrictAdjunction U.ι).unit.app F ≫ P.map (R.resolution.ι.f 0) ≫ 𝟙 _
      rw [Category.comp_id]
      exact hβ
    a := a
    sections := by intro n; rfl
    invertible := by
      intro q
      simp only [CategoryTheory.Functor.map_id, Category.comp_id]
      infer_instance }
  have hC : moduleCohomologyRestriction U F p = C.map p := by
    exact moduleCohomologyFMap_independent U.ι ((restrictAdjunction U.ι).unit.app F)
      (Classical.choice (moduleCohomologyFMapData_nonempty U.ι F _ _)) C p
  let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let r := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
      ((CategoryTheory.evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map
        (homOfLE (show U ≤ ⊤ from le_top)).op)) (ComplexShape.up ℕ)).app I.cocomplex
  have hc : (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map β ≫
      a.inv ≫ R.sections.hom = r := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, R.components]
    exact restriction_component U (I.cocomplex.X n) (R.resolution.cocomplex.X n)
      ((HomologicalComplex.eval _ _ n).mapIso R.comparison)
  let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  rw [hC]
  dsimp only [ModuleCohomologyFMapData.map, C]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  have htransport := iso_homology_transport H
    ((forget₂ _ AddCommGrpCat.{u}).mapIso
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p))
    ((((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm)
    ((forget₂ _ AddCommGrpCat.{u}).mapIso
      (R.resolution.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p))
    ((((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm)
    a ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map β) R.sections.hom r hc
  exact htransport

end AlgebraicGeometry.Scheme.Modules
