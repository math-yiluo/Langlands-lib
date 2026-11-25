/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdge
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Local classes of the ordinary-unit map in a square

Source: Stacks Project, Cohomology, Tags 01E4, 01FB, 0BKJ and 0D5X.
(blueprint: def-weil-pbc-derived-square-local-models).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
private theorem map_pasting {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B L : C} {M N : D} (a : M ⟶ N) (b : N ⟶ F.obj A)
    (c : A ⟶ B) (d : B ⟶ L) :
    a ≫ b ≫ F.map (c ≫ d) = (a ≫ b ≫ F.map c) ≫ F.map d := by
  rw [F.map_comp]
  simp only [Category.assoc]

namespace AlgebraicGeometry
open Scheme.Modules

/-- Restrict an h-map, keeping the restriction of its global coefficient as target.
Source: Stacks Project, Tag 01FB
(blueprint: def-weil-pbc-derived-square-local-models). -/
def restrictedDirectImageMap {Z X : Scheme.{u}} (v : Z ⟶ X)
    {F : X.Modules} {G : Z.Modules} (φ : F ⟶ (pushforward v).obj G) (U : X.Opens) :
    (restrictFunctor U.ι).obj F ⟶
      (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).obj
        ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G) :=
  ((restrictAdjunction U.ι).homEquiv _ _).symm
    (φ ≫ (pushforward v).map ((restrictAdjunction (v ⁻¹ᵁ U).ι).unit.app G) ≫
      (pushforwardComp (v ⁻¹ᵁ U).ι v).hom.app
        ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G) ≫
      ((pushforwardComp (v.resLE U (v ⁻¹ᵁ U) le_rfl) U.ι ≪≫
        pushforwardCongr (v.resLE_comp_ι le_rfl)).inv.app
          ((restrictFunctor (v ⁻¹ᵁ U).ι).obj G)))

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The canonical total/classical comparison, with the total derived-category
universe fixed by the supplied family of scheme module categories.
Source: total/classical right-derived compatibility
(blueprint: def-weil-pbc-derived-square-local-models). -/
def schemeSingleCohomologyComparison {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (q : ℕ) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) ≅
      ((pushforward f).rightDerived q).obj F :=
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F q

/-- Inverse-open hypercohomology, evaluated upstairs on the same K-injective model.
Source: Stacks Project, Tag 0D5X
(blueprint: def-weil-pbc-derived-square-local-models). -/
@[irreducible] def squareInverseOpenComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℤ)
    (K : schemeDerivedCategory X) :
    (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom q).obj K ≅
      (TopologicalSpace.Opens.map f.base).op ⋙
        (RingedSpace.localHypercohomologyPresheaf X.toRingedSpace q).obj K :=
  RingedSpace.topEdgeInverseModel f.toLRSHom.toShHom q K ≪≫
    (((Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map f.base).op).mapHomologicalComplexHomologyIso
        (ComplexShape.up ℤ) q).app
          (((RingedSpace.localAbelianSections X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (RingedSpace.topEdgeResolution X.toRingedSpace K)) ≪≫
    ((Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map f.base).op).mapIso
        (RingedSpace.topEdgeLocalModel X.toRingedSpace q K).symm

attribute [local irreducible] RingedSpace.topEdgeInverseModel
  RingedSpace.topEdgeLocalModel RingedSpace.topEdgeLocalClass

/-- The inverse-open comparison carries the inverse-open class map to the class map
upstairs. This equation unfolds the comparison exactly once.
Source: Stacks Project, Tag 0D5X
(blueprint: def-weil-pbc-derived-square-local-models). -/
theorem squareInverseOpenComparison_class {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℤ)
    (K : schemeDerivedCategory X) :
    RingedSpace.topEdgeInverseLocalClass f.toLRSHom.toShHom q K =
      (squareInverseOpenComparison f q K).hom ≫
        Functor.whiskerLeft (TopologicalSpace.Opens.map f.base).op
          (RingedSpace.topEdgeLocalClass X.toRingedSpace q K) := by
  unfold RingedSpace.topEdgeInverseLocalClass squareInverseOpenComparison
  exact map_pasting
    ((Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map f.base).op)
    (RingedSpace.topEdgeInverseModel f.toLRSHom.toShHom q K).hom
    ((((Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map f.base).op).mapHomologicalComplexHomologyIso
        (ComplexShape.up ℤ) q).hom.app
          (((RingedSpace.localAbelianSections X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (RingedSpace.topEdgeResolution X.toRingedSpace K)))
    (RingedSpace.topEdgeLocalModel X.toRingedSpace q K).inv
    (RingedSpace.topEdgeLocalClass X.toRingedSpace q K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit local section comparison through an augmentation-normalized resolution.
Source: Stacks Project, Tags 01E4 and 0D5X
(blueprint: def-weil-pbc-derived-square-local-models). -/
@[irreducible] def squareLocalResolutionComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (q : ℕ) (V : Y.Opens) (I : InjectiveResolution F)
    (U : X.Opens) (hU : U = f ⁻¹ᵁ V) (R : RestrictedResolutionSections I U) :
    (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace q).obj
          ((restrictFunctor U.ι).obj F)) ≅
      ((RingedSpace.localHypercohomologyPresheaf Y.toRingedSpace (q : ℤ)).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))).obj (op V) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  letI : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  letI := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let Γ := RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)
  letI : Γ.Additive := inferInstanceAs
    (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).Additive
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q
  let E := (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections Y.toRingedSpace
  letI : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  have : QuasiIso I.ι' := inferInstance
  have : IsIso ((DerivedCategory.Q.{w} (C := X.Modules)).map I.ι') := inferInstance
  let r : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F ≅
      DerivedCategory.Q.obj I.cochainComplex :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app F ≪≫ asIso (DerivedCategory.Q.map I.ι')
  let b : (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom
      (q : ℤ)).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ≅
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).homology
        (q : ℤ) :=
    (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom
      (q : ℤ)).mapIso r ≪≫
    (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace) (𝟙 I.cochainComplex)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).app _
  let a := (forget₂ _ AddCommGrpCat.{u}).mapIso
      (R.resolution.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) q) ≪≫
    (((RingedSpace.globalSectionsComplex R.resolution).sc q).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm ≪≫
    H.mapIso (R.sections ≪≫ eqToIso (congrArg (fun W ↦
      ((RingedSpace.openModuleSections X.toRingedSpace W).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex) hU)) ≪≫
    (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (q : ℤ)).mapIso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat Γ).symm
  exact a ≪≫
    (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).sc
      (q : ℤ)).mapHomologyIso E ≪≫ E.mapIso b.symm ≪≫
    E.mapIso (RingedSpace.topEdgeLocalLeray f.toLRSHom.toShHom (q : ℤ)
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).symm

end AlgebraicGeometry
