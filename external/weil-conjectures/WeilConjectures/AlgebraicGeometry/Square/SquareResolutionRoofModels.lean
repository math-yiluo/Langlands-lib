/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClassModels

/-! # Separate the classical and total resolution comparisons

Source: Stacks Project, Cohomology, Tags 01E4, 01FB and 0D5X.
(blueprint: def-weil-pbc-square-resolution-roof-models).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w vD uD vE uE vB uB
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

/-- Classical cohomology on an open, computed by the integer extension of its fixed
restricted resolution. All comparisons preserve the augmentation.
Source: Stacks Project, Tags 01E4 and 01FB
(blueprint: def-weil-pbc-square-resolution-roof-models). -/
@[irreducible] def squareResolutionCohomologyIso {X : Scheme.{u}} {F : X.Modules}
    (I : InjectiveResolution F) (U : X.Opens) (R : RestrictedResolutionSections I U)
    (q : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace q).obj
          ((restrictFunctor U.ι).obj F)) ≅
      (((RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.cochainComplex).homology (q : ℤ) := by
  letI := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let Γ := RingedSpace.openModuleSections X.toRingedSpace U
  letI : Γ.Additive := inferInstanceAs
    (RingedSpace.openModuleSections X.toRingedSpace U).Additive
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q
  exact (forget₂ _ AddCommGrpCat.{u}).mapIso
      (R.resolution.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) q) ≪≫
    (((RingedSpace.globalSectionsComplex R.resolution).sc q).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm ≪≫
    H.mapIso R.sections ≪≫
    (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (q : ℤ)).mapIso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat Γ).symm

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Local hypercohomology of a direct image, computed on the fixed injective resolution
upstairs. This involves no restricted resolution or classical cohomology.
Source: Stacks Project, Tag 0D5X
(blueprint: def-weil-pbc-square-resolution-roof-models). -/
@[irreducible] def squareInjectiveLocalComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (q : ℕ) (V : Y.Opens) (I : InjectiveResolution F)
    (U : X.Opens) (hU : U = f ⁻¹ᵁ V) :
    (((RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.cochainComplex).homology (q : ℤ) ≅
      ((RingedSpace.localHypercohomologyPresheaf Y.toRingedSpace (q : ℤ)).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))).obj (op V) := by
  subst U
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf, Scheme.Modules.instCategory,
    Scheme.Modules.Hom] at *
  let E := (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections Y.toRingedSpace
  letI : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  let aug : (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F ⟶
      (show CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ from
        I.cochainComplex) := I.ι'
  have haug : QuasiIso aug := by
    simpa only [aug, Scheme.Modules, Scheme.Modules.instCategory, Scheme.Modules.Hom] using
      (inferInstanceAs (QuasiIso I.ι'))
  let t := (DerivedCategory.Q.{w, u, u + 1} (C := SheafOfModules.{u}
    (moduleRings X.toRingedSpace))).map aug
  have ht : IsIso t := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) aug).2
    exact haug
  let r : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F ≅
      (DerivedCategory.Q.{w, u, u + 1} (C := SheafOfModules.{u}
        (moduleRings X.toRingedSpace))).obj I.cochainComplex :=
    (DerivedCategory.singleFunctorIsoCompQ.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app F ≪≫ @asIso _ _ _ _ t ht
  letI : CochainComplex.IsKInjective
      (show CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ from
        I.cochainComplex) := CochainComplex.isKInjective_of_injective I.cochainComplex 0
  letI : QuasiIso (𝟙 (show CochainComplex (SheafOfModules.{u}
      (moduleRings X.toRingedSpace)) ℤ from I.cochainComplex)) := by infer_instance
  let b : (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom
      (q : ℤ)).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ≅
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).homology
        (q : ℤ) :=
    (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom
      (q : ℤ)).mapIso r ≪≫
    (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace)
        (𝟙 (show CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ from
          I.cochainComplex))) ≪≫
    (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).app _
  exact (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).sc
      (q : ℤ)).mapHomologyIso E ≪≫ E.mapIso b.symm ≪≫
    E.mapIso (RingedSpace.topEdgeLocalLeray f.toLRSHom.toShHom (q : ℤ)
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).symm

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory Scheme.Modules.instAbelian TopCat.Sheaf

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The published comparison is the classical section comparison followed by the
comparison computing total direct image on the same injective complex.
Source: Stacks Project, Tags 01E4 and 0D5X
(blueprint: def-weil-pbc-square-resolution-roof-models). -/
theorem squareLocalResolutionComparison_factor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (q : ℕ) (V : Y.Opens) (I : InjectiveResolution F)
    (U : X.Opens) (hU : U = f ⁻¹ᵁ V) (R : RestrictedResolutionSections I U) :
    (squareLocalResolutionComparison f F q V I U hU R).hom =
      (squareResolutionCohomologyIso I U R q).hom ≫
        (squareInjectiveLocalComparison f F q V I U hU).hom := by
  subst U
  unfold squareLocalResolutionComparison squareResolutionCohomologyIso
    squareInjectiveLocalComparison
  dsimp only [id]
  simp only [Iso.trans_hom, Category.assoc]
  rfl

end AlgebraicGeometry
