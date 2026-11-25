/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedTensorData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
/-! # Canonical derived section-module realization

## Main definitions

- `derivedEquivalence`: localization of the fixed section equivalence.
- `derivedPullback`, `derivedPushforward`: actual ringed derived operations.
- `tensor`, `tensorComparison`, `qTensor`: the normalized K-flat tensor realization.
- `tensorPullComparison`: the uniquely specified ringed tensor-pullback map.
- `derivedExtension`, `derivedOpenAdjunction`: localized open extension and restriction.
- `derivedPullbackComposition`: localization of geometric pullback pasting.

## References

* Stacks Project, Sites, Tag 00YV
* Modules on Sites, Tags 03EK, 03EL, 03D7, 03DI and 03DJ
* Cohomology on Sites, Tags 07A4, 07A6 and 0B56
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.all false
set_option linter.mathlibStandardSet false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local instance] sectionFunctorAdditive

attribute [local irreducible] ordinaryTensorComparison totalComparison tensorComparison
  Functor.mapDerivedCategory

attribute [local irreducible] tensor

attribute [local irreducible] CategoryTheory.Localization.Monoidal.tensorBifunctor
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

set_option allowUnsafeReducibility true in
attribute [local irreducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex

set_option linter.unusedSectionVars false in
private theorem section_kflat_iff (X : Scheme.{u})
    (P : CochainComplex (internalModules Λ X) ℤ) :
    (∀ Z : CochainComplex (internalModules Λ X) ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z P (curriedTensor _)).Acyclic) ↔
        CochainComplex.IsKFlatIndependentCoefficients
          (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  exact InternalAbelianSheafModule.comparison_kflat
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) P

set_option linter.unusedSectionVars false in
private theorem internal_kflat_image (X : Scheme.{u})
    (P : CochainComplex (internalModules Λ X) ℤ)
    (hP : (HomotopyCategory.quasiIso (internalModules Λ X) (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ _).obj P)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply (section_kflat_iff Λ X P).mp
  intro Z hZ
  have h := ((HomotopyCategory.kFlat_iff_preserves_acyclic _).mp hP
    ((HomotopyCategory.quotient _ _).obj Z)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).2 hZ)).2
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 h

set_option linter.unusedSectionVars false in
private theorem independent_kflat_of_iso (X : Scheme.{u})
    {P Q : CochainComplex (modules Λ X) ℤ} (e : P ≅ Q)
    (hP : P.IsKFlatIndependentCoefficients) : Q.IsKFlatIndependentCoefficients := by
  intro Z hZ n
  exact (hP Z hZ n).of_iso (((curriedTensor (modules Λ X)).map₂CochainComplex.obj Z).mapIso e)

private theorem flat_resolving_aux
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [IsGrothendieckAbelian.{v₂} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Additive] [F.PreservesFlat] [F.IsLeftAdjoint]
    (P : CochainComplex C ℤ) :
    ∃ (A : CochainComplex C ℤ) (r : A ⟶ P), QuasiIso r ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat A ∧
      (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomologicalComplex (.up ℤ)).obj A) := by
  let L : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  exact ⟨L.reduced.resolutionFunctor.obj P, L.reduced.resolutionNatTrans.app P,
    inferInstance,
    L.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P,
    F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj L.reduced
      ObjectProperty.flat.essImage_ι_le P⟩

set_option linter.unusedSectionVars false in
private theorem pullback_resolving_complexes {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (modules Λ Y) ℤ) :
    ∃ (R : CochainComplex (modules Λ Y) ℤ) (r : R ⟶ P),
      QuasiIso r ∧ R.IsKFlatIndependentCoefficients ∧
        CochainComplex.IsKFlatIndependentCoefficients
          (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj R) := by
  let E := (equivalence Λ Y).mapHomologicalComplex (.up ℤ)
  obtain ⟨A, s, hs, hA, hFA⟩ := flat_resolving_aux
    (C := internalModules Λ Y) (D := internalModules Λ X)
    (CondensedRing.upperStar Λ f) (E.inverse.obj P)
  let r : E.functor.obj A ⟶ P := E.functor.map s ≫ E.counitIso.hom.app P
  have hA' := (HomotopyCategory.kFlat_quotient_obj_iff A).2 hA
  have hFA' := (HomotopyCategory.kFlat_quotient_obj_iff _).2 hFA
  refine ⟨E.functor.obj A, r, ?_, internal_kflat_image Λ Y A hA', ?_⟩
  · have h₂ : QuasiIso (E.functor.map s) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology s (equivalence Λ Y).functor
    have h₃ : QuasiIso (E.counitIso.hom.app P) := inferInstance
    dsimp only [r]
    infer_instance
  · have h := internal_kflat_image Λ X _ hFA'
    have hh := independent_kflat_of_iso Λ X
      ((NatIso.mapHomologicalComplex (pullComparison Λ f) (.up ℤ)).app A) h
    exact hh

@[irreducible] private def uncurryTotalComparisonIso
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {TC : C ⥤ C ⥤ C} [TC.PreservesZeroMorphisms]
    [∀ M, (TC.obj M).PreservesZeroMorphisms]
    {TD : D ⥤ D ⥤ D} [TD.PreservesZeroMorphisms]
    [∀ M, (TD.obj M).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex C ℤ, P.HasMapBifunctor Q TC]
    [∀ P Q : CochainComplex D ℤ, P.HasMapBifunctor Q TD]
    (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj F).obj TC ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TD)
    [∀ M N, IsIso ((τ.app M).app N)] :
    Functor.uncurry.obj TC.map₂CochainComplex ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TD.map₂CochainComplex := by
  refine NatIso.ofComponents
    (fun K ↦ asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) K.1 K.2)) ?_
  intro M N f
  let G := F.mapHomologicalComplex (.up ℤ)
  change G.map
      (HomologicalComplex.mapBifunctorMap f.1 (𝟙 M.2) TC (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 N.1) f.2 TC (.up ℤ)) ≫
      HomologicalComplex.mapBifunctorComparison τ (.up ℤ) N.1 N.2 =
    HomologicalComplex.mapBifunctorComparison τ (.up ℤ) M.1 M.2 ≫
      (HomologicalComplex.mapBifunctorMap (G.map f.1) (𝟙 (G.obj M.2)) TD (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 (G.obj N.1)) (G.map f.2) TD (.up ℤ))
  have h₁ := HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) f.1 (𝟙 M.2)
  have h₂ := HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) (𝟙 N.1) f.2
  rw [Functor.map_comp, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]
  dsimp only [G]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

private theorem uncurryTotalComparisonIso_hom
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {TC : C ⥤ C ⥤ C} [TC.PreservesZeroMorphisms]
    [∀ M, (TC.obj M).PreservesZeroMorphisms]
    {TD : D ⥤ D ⥤ D} [TD.PreservesZeroMorphisms]
    [∀ M, (TD.obj M).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex C ℤ, P.HasMapBifunctor Q TC]
    [∀ P Q : CochainComplex D ℤ, P.HasMapBifunctor Q TD]
    (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj F).obj TC ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TD)
    [∀ M N, IsIso ((τ.app M).app N)] (A B : CochainComplex C ℤ) :
    (uncurryTotalComparisonIso F τ).hom.app (A, B) =
      HomologicalComplex.mapBifunctorComparison τ (.up ℤ) A B := by
  unfold uncurryTotalComparisonIso
  rfl

@[irreducible] private def localization_single_iso
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{v₂} D]
    (e : C ≌ D) [e.functor.Additive] (M : C) (N : D) (e₀ : e.functor.obj M ≅ N) :
    e.functor.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      (DerivedCategory.singleFunctor D 0).obj N :=
  e.functor.mapDerivedCategoryFactors.app ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex e.functor (.up ℤ) 0).app M ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso e₀)

attribute [local instance] sectionOrdinaryTensorMap_isIso

@[irreducible] private def sectionTotalNatIso (X : Scheme.{u}) :
    internalTotalTensor Λ X ⋙ (equivalence Λ X).functor.mapHomologicalComplex (.up ℤ) ≅
      ((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).prod
        ((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)) ⋙ totalTensor Λ X :=
  uncurryTotalComparisonIso (equivalence Λ X).functor (sectionOrdinaryTensorMap Λ X)

private theorem sectionTotalNatIso_hom (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (sectionTotalNatIso Λ X).hom.app (P, Q) = sectionTotalComparison Λ X P Q := by
  unfold sectionTotalNatIso sectionTotalComparison
  exact uncurryTotalComparisonIso_hom (equivalence Λ X).functor
    (sectionOrdinaryTensorMap Λ X) P Q

private theorem kflat_from_acyclic_test
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ)
    (hP : ∀ Z : CochainComplex C ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z P (curriedTensor C)).Acyclic) :
    (HomotopyCategory.quasiIso C (.up ℤ)).kFlat ((HomotopyCategory.quotient _ _).obj P) := by
  rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP Z hZ)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

private theorem localization_mu_iso
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{v₁} C]
    (P Q : CochainComplex C ℤ)
    (h : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
        ((HomotopyCategory.quotient _ _).obj P) ∨
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
        ((HomotopyCategory.quotient _ _).obj Q)) :
    IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) P Q) := by
  have hm : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.quotient _ _).obj Q)) := by
    rcases h with h | h
    · exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ)) _ _ h
    · exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ)) _ _ h
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
    DerivedCategory.Qh.map _) ≫ _)
  infer_instance

private theorem internal_mu_iso (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients
        (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P) ∨
      CochainComplex.IsKFlatIndependentCoefficients
        (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj Q)) :
    IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := internalModules Λ X)) P Q) := by
  apply localization_mu_iso P Q
  exact h.imp
    (fun h ↦ kflat_from_acyclic_test P ((section_kflat_iff Λ X P).mpr h))
    (fun h ↦ kflat_from_acyclic_test Q ((section_kflat_iff Λ X Q).mpr h))

private theorem representative_iso_of_image
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F G : D ⥤ E) (q : F ⟶ G) (e : C ≌ D) (X : D)
    (h : IsIso (q.app (e.functor.obj (e.inverse.obj X)))) : IsIso (q.app X) := by
  have := h
  have heq : q.app X = F.map (e.counitIso.inv.app X) ≫
      q.app (e.functor.obj (e.inverse.obj X)) ≫ G.map (e.counitIso.hom.app X) := by
    rw [← q.naturality, ← F.map_comp_assoc, e.counitIso.inv_hom_id_app, F.map_id,
      Category.id_comp]
    rfl
  rw [heq]
  infer_instance

private def TensorMapNormalization
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ D) (Qi : C ⥤ C') (Qs : D ⥤ D') (F : C' ⥤ D')
    (B : C' × C' ⥤ C') (Bs : D' × D' ⥤ D')
    (T : C × C ⥤ C) (Ts : D × D ⥤ D)
    (k : Qi ⋙ F ≅ e.functor ⋙ Qs)
    (c : B ⋙ F ≅ (F.prod F) ⋙ Bs)
    (β : ∀ P Q : C, (T ⋙ e.functor).obj (P, Q) ⟶
      ((e.functor.prod e.functor) ⋙ Ts).obj (P, Q))
    (γ : ∀ P Q : C, B.obj (Qi.obj P, Qi.obj Q) ⟶ Qi.obj (T.obj (P, Q)))
    (q : (Qs.prod Qs) ⋙ Bs ⟶ Ts ⋙ Qs) : Prop :=
  ∀ P Q : C, q.app (e.functor.obj P, e.functor.obj Q) =
    Bs.map (Prod.mkHom (k.app P).inv (k.app Q).inv) ≫
      c.inv.app (Qi.obj P, Qi.obj Q) ≫ F.map (γ P Q) ≫
      k.hom.app (T.obj (P, Q)) ≫ Qs.map (β P Q)

private def TensorMapIsoOnImages
    {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) (F G : D × D ⥤ E) (q : F ⟶ G) (P : C → C → Prop) : Prop :=
  ∀ A B : C, P A B → IsIso (q.app (e.functor.obj A, e.functor.obj B))

private abbrev TensorMapSpec
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ D) (Qi : C ⥤ C') (Qs : D ⥤ D') (F : C' ⥤ D')
    (B : C' × C' ⥤ C') (Bs : D' × D' ⥤ D')
    (T : C × C ⥤ C) (Ts : D × D ⥤ D)
    (k : Qi ⋙ F ≅ e.functor ⋙ Qs)
    (c : B ⋙ F ≅ (F.prod F) ⋙ Bs)
    (β : ∀ P Q : C, (T ⋙ e.functor).obj (P, Q) ⟶
      ((e.functor.prod e.functor) ⋙ Ts).obj (P, Q))
    (γ : ∀ P Q : C, B.obj (Qi.obj P, Qi.obj Q) ⟶ Qi.obj (T.obj (P, Q)))
    (q : (Qs.prod Qs) ⋙ Bs ⟶ Ts ⋙ Qs) : Prop :=
  TensorMapNormalization e Qi Qs F B Bs T Ts k c β γ q ∧
    TensorMapIsoOnImages e ((Qs.prod Qs) ⋙ Bs) (Ts ⋙ Qs) q (fun P Q ↦ IsIso (γ P Q))

private theorem transport_tensor_representative
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ D) (Qi : C ⥤ C') (Qs : D ⥤ D') (F : C' ⥤ D')
    (B : C' × C' ⥤ C') (Bs : D' × D' ⥤ D')
    (T : C × C ⥤ C) (Ts : D × D ⥤ D)
    (k : Qi ⋙ F ≅ e.functor ⋙ Qs)
    (c : B ⋙ F ≅ (F.prod F) ⋙ Bs)
    (b : T ⋙ e.functor ≅ (e.functor.prod e.functor) ⋙ Ts)
    (m : (Qi.prod Qi) ⋙ B ⟶ T ⋙ Qi)
    (β : ∀ P Q : C, (T ⋙ e.functor).obj (P, Q) ⟶
      ((e.functor.prod e.functor) ⋙ Ts).obj (P, Q))
    (hβ : ∀ P Q, b.hom.app (P, Q) = β P Q)
    (γ : ∀ P Q : C, B.obj (Qi.obj P, Qi.obj Q) ⟶ Qi.obj (T.obj (P, Q)))
    (hγ : ∀ P Q, m.app (P, Q) = γ P Q) :
    ∃ q : (Qs.prod Qs) ⋙ Bs ⟶ Ts ⋙ Qs,
      TensorMapSpec e Qi Qs F B Bs T Ts k c β γ q := by
  let kp : (Qi.prod Qi) ⋙ (F.prod F) ≅
      (e.functor.prod e.functor) ⋙ (Qs.prod Qs) := NatIso.prod k k
  let l : T ⋙ Qi ⋙ F ≅ (e.functor.prod e.functor) ⋙ Ts ⋙ Qs :=
    Functor.isoWhiskerLeft T k ≪≫ Functor.isoWhiskerRight b Qs
  let w : (e.functor.prod e.functor) ⋙ ((Qs.prod Qs) ⋙ Bs) ⟶
      (e.functor.prod e.functor) ⋙ (Ts ⋙ Qs) :=
    (Functor.isoWhiskerRight kp.symm Bs).hom ≫
      (Functor.isoWhiskerLeft (Qi.prod Qi) c.symm).hom ≫
      Functor.whiskerRight m F ≫ l.hom
  let W := (Functor.whiskeringLeft _ _ D').obj (e.functor.prod e.functor)
  letI : W.IsEquivalence := (Equivalence.congrLeft (E := D') (e.prod e)).isEquivalence_inverse
  let q := W.preimage w
  have hq : Functor.whiskerLeft (e.functor.prod e.functor) q = w := by
    exact W.map_preimage w
  have hn (P Q : C) := NatTrans.congr_app hq (P, Q)
  refine ⟨q, ?_, ?_⟩
  · intro P Q
    simpa only [w, kp, l, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Iso.trans_hom, Iso.symm_hom, NatIso.ofComponents_hom_app, Category.assoc,
      NatIso.prod, NatTrans.prod, Iso.app_inv, Iso.app_hom,
      Functor.prod_obj, Functor.comp_obj, hβ, hγ] using hn P Q
  · intro P Q hm
    have : IsIso (m.app (P, Q)) := by
      rw [hγ]
      exact hm
    rw [show q.app (e.functor.obj P, e.functor.obj Q) = w.app (P, Q) from hn P Q]
    dsimp only [w, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance

private theorem transport_tensor_representative_complete
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ D) (Qi : C ⥤ C') (Qs : D ⥤ D') (F : C' ⥤ D')
    (B : C' × C' ⥤ C') (Bs : D' × D' ⥤ D')
    (T : C × C ⥤ C) (Ts : D × D ⥤ D)
    (k : Qi ⋙ F ≅ e.functor ⋙ Qs)
    (c : B ⋙ F ≅ (F.prod F) ⋙ Bs)
    (b : T ⋙ e.functor ≅ (e.functor.prod e.functor) ⋙ Ts)
    (m : (Qi.prod Qi) ⋙ B ⟶ T ⋙ Qi)
    (β : ∀ P Q : C, (T ⋙ e.functor).obj (P, Q) ⟶
      ((e.functor.prod e.functor) ⋙ Ts).obj (P, Q))
    (hβ : ∀ P Q, b.hom.app (P, Q) = β P Q)
    (γ : ∀ P Q : C, B.obj (Qi.obj P, Qi.obj Q) ⟶ Qi.obj (T.obj (P, Q)))
    (hγ : ∀ P Q, m.app (P, Q) = γ P Q)
    (S : D → Prop) (hS : ∀ X, S X → S (e.functor.obj (e.inverse.obj X)))
    (hm : ∀ P Q : C, S (e.functor.obj P) ∨ S (e.functor.obj Q) → IsIso (γ P Q))
    (U V : D') (hU : Nonempty (U ≅ V)) :
    ∃ q : (Qs.prod Qs) ⋙ Bs ⟶ Ts ⋙ Qs,
      TensorMapNormalization e Qi Qs F B Bs T Ts k c β γ q ∧
        (∀ P Q : D, S P ∨ S Q → IsIso (q.app (P, Q))) ∧ Nonempty (U ≅ V) := by
  obtain ⟨q, hq⟩ := transport_tensor_representative e Qi Qs F B Bs T Ts k c b m β hβ γ hγ
  refine ⟨q, hq.1, ?_, hU⟩
  intro P Q h
  have hh : S (e.functor.obj (e.inverse.obj P)) ∨
      S (e.functor.obj (e.inverse.obj Q)) := h.imp (hS P) (hS Q)
  exact representative_iso_of_image _ _ q (e.prod e) (P, Q)
    (hq.2 _ _ (hm _ _ hh))

attribute [local irreducible] derivedEquivalence

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] derivedEquivalence

private theorem natTrans_eq_on_equivalence
    {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) {F G : D ⥤ E} (α β : F ⟶ G)
    (h : ∀ X : C, α.app (e.functor.obj X) = β.app (e.functor.obj X)) : α = β := by
  let W := (Functor.whiskeringLeft _ _ E).obj e.functor
  letI : W.IsEquivalence := (Equivalence.congrLeft (E := E) e).isEquivalence_inverse
  apply W.map_injective
  apply NatTrans.ext
  exact funext h

attribute [local irreducible] qTensor totalPullComparison

private theorem qTensor_spec (X : Scheme.{u}) :
    TensorRepresentativeCondition Λ X (qTensor Λ X) := by
  unfold qTensor
  exact (tensor_representatives Λ X).exists.choose_spec

@[irreducible] private def totalPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    totalTensor Λ Y ⋙ (pullback Λ f).mapHomologicalComplex (.up ℤ) ≅
      (((pullback Λ f).mapHomologicalComplex (.up ℤ)).prod
        ((pullback Λ f).mapHomologicalComplex (.up ℤ))) ⋙ totalTensor Λ X :=
  uncurryTotalComparisonIso (pullback Λ f)
    (Functor.OplaxMonoidal.δNatTrans (pullback Λ f))

private theorem totalPullIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (totalPullIso Λ f).hom.app (P, Q) = totalPullComparison Λ f P Q := by
  unfold totalPullIso totalPullComparison
  exact uncurryTotalComparisonIso_hom (pullback Λ f)
    (Functor.OplaxMonoidal.δNatTrans (pullback Λ f)) P Q

private theorem representative_square_iff {C : Type*} [Category C]
    {A B D E G H : C} (x : A ⟶ B) [IsIso x] (y : G ⟶ H) [IsIso y]
    (a : A ⟶ D) (b : D ⟶ G) (c : B ⟶ E) (d : E ⟶ H) :
    inv x ≫ a ≫ b = c ≫ d ≫ inv y ↔ x ≫ c ≫ d = a ≫ b ≫ y := by
  constructor
  · intro h
    have hh := congrArg (fun k ↦ x ≫ k ≫ y) h
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id,
      Category.comp_id] using hh.symm
  · intro h
    have hh := congrArg (fun k ↦ inv x ≫ k ≫ inv y) h
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id,
      Category.comp_id] using hh.symm

private theorem representative_square_map_iff
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {E G H I : D} (x : A ⟶ B) [IsIso x] (y : H ⟶ I) [IsIso y]
    (a : F.obj A ⟶ E) (b : E ⟶ H) (c : F.obj B ⟶ G) (d : G ⟶ I) :
    F.map (inv x) ≫ a ≫ b = c ≫ d ≫ inv y ↔ F.map x ≫ c ≫ d = a ≫ b ≫ y := by
  rw [Functor.map_inv]
  exact representative_square_iff (F.map x) y a b c d

private theorem pairResolution
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (T : D × D ⥤ E) (P : C → Prop)
    (hr : ∀ X, ∃ (R : C) (r : R ⟶ X), P R ∧ IsIso (Q.map r))
    (X : C × C) : ∃ (R : C × C) (r : R ⟶ X),
      (P R.1 ∧ P R.2) ∧ IsIso (((Q.prod Q) ⋙ T).map r) := by
  obtain ⟨R, r, hR, hi⟩ := hr X.1
  obtain ⟨S, s, hS, hj⟩ := hr X.2
  have := hi
  have := hj
  have : IsIso (Prod.mkHom (Q.map r) (Q.map s)) :=
    (isIso_prod_iff (f := Prod.mkHom (Q.map r) (Q.map s))).mpr
      ⟨inferInstance, inferInstance⟩
  refine ⟨(R, S), Prod.mkHom r s, ⟨hR, hS⟩, ?_⟩
  change IsIso (T.map (Prod.mkHom (Q.map r) (Q.map s)))
  infer_instance

private theorem natTrans_eq_of_resolutions
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (a b : F ⟶ G) (P : C → Prop)
    (hr : ∀ X, ∃ (T : C) (f : T ⟶ X), P T ∧ IsIso (F.map f))
    (h : ∀ X, P X → a.app X = b.app X) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨T, f, hT, hf⟩ := hr X
  have := hf
  apply (cancel_epi (F.map f)).mp
  rw [a.naturality, b.naturality, h T hT]

private theorem tensorComparisonDescentAll
    {K H D E : Type*} [Category K] [Category H] [Category D] [Category E]
    (q : K ⥤ D) (q' : H ⥤ E) (F : K ⥤ H) (LF : D ⥤ E)
    (eps : q ⋙ LF ⟶ F ⋙ q')
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hF : ∀ X, P X → S (F.obj X))
    (ff : ((Functor.whiskeringLeft _ _ E).obj
      ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    (t : K × K ⥤ K) (t' : H × H ⥤ H)
    (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (a : (q.prod q) ⋙ T ⟶ t ⋙ q) (a' : (q'.prod q') ⋙ T' ⟶ t' ⋙ q')
    (b : t ⋙ F ≅ (F.prod F) ⋙ t')
    (β : ∀ X Y : K, F.obj (t.obj (X, Y)) ⟶ t'.obj (F.obj X, F.obj Y))
    (hβ : ∀ X Y, b.hom.app (X, Y) = β X Y)
    (he : ∀ X, IsIso (eps.app X))
    (ha : ∀ X Y, P X → IsIso (a.app (X, Y)))
    (ha' : ∀ X Y, S X → IsIso (a'.app (X, Y)))
    (hr : ∀ X, ∃ (R : K) (r : R ⟶ X), P R ∧ IsIso (q.map r)) :
    ∃! d : T ⋙ LF ≅ (LF.prod LF) ⋙ T',
      ∀ X Y, LF.map (a.app (X, Y)) ≫ eps.app (t.obj (X, Y)) ≫
        q'.map (β X Y) =
      d.hom.app (q.obj X, q.obj Y) ≫
        T'.map (Prod.mkHom (eps.app X) (eps.app Y)) ≫ a'.app (F.obj X, F.obj Y) := by
  let aP := Functor.whiskerLeft (P.ι.prod P.ι) a
  let aS := Functor.whiskerLeft (S.ι.prod S.ι) a'
  have (Z : P.FullSubcategory × P.FullSubcategory) : IsIso (aP.app Z) :=
    ha Z.1.obj Z.2.obj Z.1.property
  have (Z : S.FullSubcategory × S.FullSubcategory) : IsIso (aS.app Z) :=
    ha' Z.1.obj Z.2.obj Z.1.property
  have : IsIso aP := NatIso.isIso_of_isIso_app aP
  have : IsIso aS := NatIso.isIso_of_isIso_app aS
  let r := (asIso aP).symm
  let r' := (asIso aS).symm
  obtain ⟨d, hd, hu⟩ := tensorComparisonDescent q q' F LF eps P S hF ff
    t t' T T' r r' b (fun X _ ↦ he X) (fun X Y _ _ ↦ he (t.obj (X, Y)))
  let l : (q.prod q) ⋙ T ⋙ LF ⟶ (F.prod F) ⋙ t' ⋙ q' :=
    Functor.whiskerRight a LF ≫ Functor.whiskerLeft t eps ≫
      Functor.whiskerRight b.hom q'
  let rr (d : T ⋙ LF ≅ (LF.prod LF) ⋙ T') :
      (q.prod q) ⋙ T ⋙ LF ⟶ (F.prod F) ⋙ t' ⋙ q' :=
    Functor.whiskerLeft (q.prod q) d.hom ≫
      Functor.whiskerRight (NatTrans.prod eps eps) T' ≫
      Functor.whiskerLeft (F.prod F) a'
  have hrule (d : T ⋙ LF ≅ (LF.prod LF) ⋙ T') (X Y : K) :
      l.app (X, Y) = (rr d).app (X, Y) ↔
      LF.map (a.app (X, Y)) ≫ eps.app (t.obj (X, Y)) ≫ q'.map (b.hom.app (X, Y)) =
        d.hom.app (q.obj X, q.obj Y) ≫
        T'.map (Prod.mkHom (eps.app X) (eps.app Y)) ≫ a'.app (F.obj X, F.obj Y) :=
    by
      simp only [l, rr, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
        NatIso.prod, NatTrans.prod, NatIso.ofComponents_hom_app,
        asIso_hom, Functor.prod_obj]
  have hs (X Y : K) (hX : P X) (hY : P Y) : l.app (X, Y) = (rr d).app (X, Y) := by
    have := ha X Y hX
    have := ha' (F.obj X) (F.obj Y) (hF X hX)
    apply (hrule d X Y).mpr
    apply (representative_square_map_iff LF (a.app (X, Y))
      (a'.app (F.obj X, F.obj Y)) _ _ _ _).mp
    simpa only [r, r', aP, aS, Functor.whiskerLeft_app, Functor.prod_obj,
      ObjectProperty.ι_obj, Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app] using
      hd X Y hX hY
  have hall : l = rr d := by
    apply natTrans_eq_of_resolutions l (rr d) (fun Z ↦ P Z.1 ∧ P Z.2)
    · exact pairResolution q (T ⋙ LF) P hr
    · rintro ⟨X, Y⟩ h
      exact hs X Y h.1 h.2
  refine ⟨d, ?_, ?_⟩
  · intro X Y
    have hh := (hrule d X Y).mp (NatTrans.congr_app hall (X, Y))
    rw [hβ] at hh
    exact hh
  intro d' hd'
  apply hu d'
  intro X Y hX hY
  have := ha X Y hX
  have := ha' (F.obj X) (F.obj Y) (hF X hX)
  have hh := hd' X Y
  rw [← hβ] at hh
  have h := (representative_square_map_iff LF (a.app (X, Y))
    (a'.app (F.obj X, F.obj Y)) _ _ _ _).mpr hh
  simpa only [r, r', aP, aS, Functor.whiskerLeft_app, Functor.prod_obj,
    ObjectProperty.ι_obj, Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app] using h

attribute [local irreducible] totalTensor

private theorem complex_resolving_whiskering
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{v₁} C]
    (E : Type u₂) [Category.{v₂} E] (P : ObjectProperty (CochainComplex C ℤ))
    (hr : ∀ R : CochainComplex C ℤ,
      ∃ (R' : CochainComplex C ℤ) (r : R' ⟶ R), P R' ∧ QuasiIso r) :
    Nonempty (((Functor.whiskeringLeft _ _ E).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun R ↦ P R.as
  have hres : ∀ R : HomotopyCategory C (.up ℤ),
      ∃ (R' : H.FullSubcategory) (r : R'.obj ⟶ R),
        HomotopyCategory.quasiIso C (.up ℤ) r := by
    intro R
    obtain ⟨R', r, hR', hr⟩ := hr R.as
    exact ⟨⟨(HomotopyCategory.quotient _ _).obj R', hR'⟩,
      (HomotopyCategory.quotient _ _).map r,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff r).2 hr⟩
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering E
    (HomotopyCategory.quotient _ _) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh P H (fun _ ↦ Iff.rfl) hres
  exact ⟨ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _))
      (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _))))⟩

/-- The existing levelwise comparison for extension by zero, fixed by its adjunction mate. -/
def extensionComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek Λ j ⋙ (equivalence Λ X).functor ≅
      (equivalence Λ U).functor ⋙ extension Λ j :=
  ordinaryExtensionComparison Λ j

/-- The levelwise ringed extension on the unbounded derived category. -/
@[implicit_reducible]
def derivedExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory (modules Λ U) ⥤ DerivedCategory (modules Λ X) :=
  (extension Λ j).mapDerivedCategory

/-- The ringed open adjunction is the localization of the specified ordinary adjunction. -/
def derivedOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedExtension Λ j ⊣ derivedPullback Λ j :=
  (openAdjunction Λ j).mapDerivedCategoryAdjunction

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
