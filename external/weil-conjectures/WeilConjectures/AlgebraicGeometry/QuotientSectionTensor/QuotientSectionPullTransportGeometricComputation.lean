/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization

/-! # Geometric computation for normalized section transport

## References

* Stacks Project, Tags 06YY, 0D6D and 07A6
* Stacks 0D6D and 07A6, the geometric computation step of normalized section transport
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Share the large inferred cochain structures while checking the diagram proof.
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

attribute [local instance] ModuleRingedComparison.sectionFunctorAdditive

attribute [local semireducible] QuotientChange.L
attribute [local implicit_reducible] QuotientChange.L
  InternalAbelianSheafModule.sectionRingSheaf
  DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.catToReflQuiver
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory

private theorem fifth_conj {a b c d e tail : Prop} (h : a ∧ b ∧ c ∧ d ∧ e ∧ tail) : e :=
  h.2.2.2.2.1

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

private theorem native_localization_hom (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    ((ModuleRingedComparison.equivalence Λ T).functor.mapDerivedCategoryFactors).hom.app P =
      (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom := by
  rfl

-- Unfold the two named interfaces once, preserving the fixed derived-functor instances.
/-- The fixed geometric comparison commutes with the two localization computation maps. -/
theorem section_pull_transport_geometric_computation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules Λ Y) ℤ) :
    @Eq ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj
      ((L Λ f).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj
        (((ModuleRingedComparison.pullback Λ f).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleRingedComparison.equivalence Λ Y).functor.mapHomologicalComplex (.up ℤ)).obj
            P)))
      ((ModuleRingedComparison.derivedEquivalence Λ X).functor.map
        ((L Λ f).map
            ((DerivedCategory.quotientCompQhIso (Modules Λ Y)).inv.app P) ≫
          (pullCounit (Λ := Λ) f).app ((HomotopyCategory.quotient _ _).obj P) ≫
          DerivedCategory.Qh.map
            (((CondensedRing.upperStar Λ f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
          (DerivedCategory.quotientCompQhIso (Modules Λ X)).hom.app
            (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      ((ModuleRingedComparison.equivalence Λ X).functor.mapDerivedCategoryFactors).hom.app
        (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ModuleRingedComparison.pullComparison Λ f)
          (.up ℤ)).hom.app P))
      ((ModuleRingedComparison.derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj P) ≫
      (ModuleRingedComparison.derivedPullback Λ f).map
        (((ModuleRingedComparison.equivalence Λ Y).functor.mapDerivedCategoryFactors).hom.app P) ≫
      ((ModuleRingedComparison.pullback Λ f).mapDerivedCategoryFactors.hom).app
        (((ModuleRingedComparison.equivalence Λ Y).functor.mapHomologicalComplex (.up ℤ)).obj P))
    := by
  have hh :=
    (fifth_conj (ModuleRingedComparison.sectionDerivedPushpullNormalization Λ f) P).symm
  unfold L CondensedRing.moduleObjectDerivedPullback pullCounit
  dsimp only [_root_.id]
  simpa only [native_localization_hom,
    ModuleRingedComparison.internalDerivedPullback, ModuleRingedComparison.comparisonSource,
    ModuleRingedComparison.derivedPullback, Functor.comp_obj] using hh

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
