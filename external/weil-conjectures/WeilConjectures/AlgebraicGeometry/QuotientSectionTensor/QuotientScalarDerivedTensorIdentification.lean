/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarDerivedOplax
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # The regular scalar unit and the derived tensor constraints -/

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

/-- The derived oplax tensorator is the canonical normalized tensorator. -/
theorem scalarDerivedOplax_δ (T : Scheme.{u})
    (M N : DerivedCategory (Modules Λ T)) :
    letI := scalarDerivedOplax a T
    Functor.OplaxMonoidal.δ (D a T) M N = (canonicalTensor a T).hom.app (M, N) := by
  unfold scalarDerivedOplax canonicalTensor D
  rfl

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
