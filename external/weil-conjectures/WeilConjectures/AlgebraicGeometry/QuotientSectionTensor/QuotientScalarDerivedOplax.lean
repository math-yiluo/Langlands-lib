/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # The regular scalar unit and the derived tensor constraints

## References

* Stacks 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

set_option backward.defeqAttrib.useBackward true
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local implicit_reducible]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory
  CategoryTheory.Sheaf.symmetricCategory CategoryTheory.Sheaf.braidedCategory

attribute [local instance 21000]
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarSheafSymmetric

attribute [local instance 2000]
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleClosed
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleBraided
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleFlat
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarPreservesKFlat

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

/-- The generic derived oplax structure, with the fixed scalar functor as its target. -/
@[irreducible] def scalarDerivedOplax (T : Scheme.{u}) : (D a T).OplaxMonoidal := by
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  have := scalarModuleFlat Λ T
  have := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  let := CondensedRing.internalScalarMonoidal a T
  have := CondensedRing.internalScalar_preservesFlat a T
  unfold D
  exact (extension a T).leftDerivedFunctorOplaxMonoidal

/-- The derived oplax unit is the specified localization-unit composite. -/
theorem scalarDerivedOplax_η (T : Scheme.{u}) :
    letI := scalarDerivedOplax a T
    Functor.OplaxMonoidal.η (D a T) = derivedScalarUnit a T := by
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  have := scalarModuleFlat Λ T
  have := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  let := CondensedRing.internalScalarMonoidal a T
  have := CondensedRing.internalScalar_preservesFlat a T
  unfold scalarDerivedOplax derivedScalarUnit D scalarCounit
  change _ ≫ _ ≫ _ ≫ _ = _
  rw [Functor.mapHomotopyCategory_η]
  rfl

/-- The derived oplax unit is invertible on the K-flat regular module. -/
theorem scalarDerivedOplax_η_isIso (T : Scheme.{u}) :
    letI := scalarDerivedOplax a T
    IsIso (Functor.OplaxMonoidal.η (D a T)) := by
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  have := scalarModuleFlat Λ T
  have := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  let := CondensedRing.internalScalarMonoidal a T
  have := CondensedRing.internalScalar_preservesFlat a T
  unfold scalarDerivedOplax D
  exact (extension a T).isIso_leftDerivedFunctorOplaxMonoidal_η

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
