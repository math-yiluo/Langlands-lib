/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
public import WeilConjectures.AlgebraicGeometry.SectionCochainTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.CategoryTheory.Monoidal.Transport
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorData

/-! # Canonical derived section-module tensor data

## Main definitions

- `derivedEquivalence`: localization of the fixed termwise section equivalence.
- `derivedPullback`, `derivedPushforward`: the actual ringed derived operations.
- `tensor`, `tensorUnit`, `tensorComparison`: normalized conjugate K-flat tensor data.
- `totalTensor`: the signed direct-sum total of the ordinary relative tensor.
- `localizedTotalComparison`: the specified total comparison after localization.

## References

* Stacks Project, Sites, Tag 00YV
* Modules on Sites, Tags 03EK, 03EL, 03D7, 03DI and 03DJ
* Cohomology on Sites, Tags 07A4, 07A6 and 0B56
* Stacks 07A4 and 06YU, fixed equivalence transport
* Stacks 06YU, fixed equivalence transport
* Stacks 06YN
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

namespace ResolvingOplaxConstraints
namespace TensorFunctorTransport

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D]

/-- The associator is the existing equivalence-transport associator. -/
theorem associator_eq (e : C ≌ D) (X Y Z : D) :
    @MonoidalCategoryStruct.associator _ _ (struct e) X Y Z =
      @MonoidalCategoryStruct.associator _ _ (Monoidal.transportStruct e) X Y Z := by
  rfl

/-- The left unitor is the existing equivalence-transport unitor. -/
theorem leftUnitor_eq (e : C ≌ D) (X : D) :
    @MonoidalCategoryStruct.leftUnitor _ _ (struct e) X =
      @MonoidalCategoryStruct.leftUnitor _ _ (Monoidal.transportStruct e) X := by
  rfl

/-- The right unitor is the existing equivalence-transport unitor. -/
theorem rightUnitor_eq (e : C ≌ D) (X : D) :
    @MonoidalCategoryStruct.rightUnitor _ _ (struct e) X =
      @MonoidalCategoryStruct.rightUnitor _ _ (Monoidal.transportStruct e) X := by
  rfl

/-- The tensor functor of the shared full structure is the shared conjugate functor. -/
theorem tensor_eq (e : C ≌ D) :
    @MonoidalCategory.tensor D _ (monoidal e) = tensorFunctor e := by
  rfl

private theorem monoidal_ext (m n : MonoidalCategory D)
    (h : m.toMonoidalCategoryStruct = n.toMonoidalCategoryStruct) : m = n := by
  cases m
  cases n
  cases h
  rfl

end TensorFunctorTransport
end ResolvingOplaxConstraints

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- The functor-level signed tensor is the same object-level signed direct-sum total. -/
theorem totalTensor_obj (X : Scheme.{u}) (P Q : CochainComplex (modules Λ X) ℤ) :
    (totalTensor Λ X).obj (P, Q) =
      CochainComplex.mapBifunctor P Q (curriedTensor (modules Λ X)) := by
  rfl

attribute [local instance] sectionFunctorAdditive sectionOrdinaryTensorMap_isIso

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
