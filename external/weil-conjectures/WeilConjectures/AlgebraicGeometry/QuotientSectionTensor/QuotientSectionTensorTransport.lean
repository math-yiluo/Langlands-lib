/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportNormalized
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportCondition

/-! # A step of the normalized quotient section comparison

## References

* Stacks 03EK, 03EL, 07A4, 06YS and 0G7D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

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

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- Tensor balancing on sections realizes every normalized internal scalar tensorator. -/
theorem section_tensor_transport (T : Scheme.{u}) (c : ScalarSectionData a T)
    (hc : ScalarSectionNormalized a T c) (b : TensorIso a T)
    (hb : TensorNormalized a T b) :
    ∃ barB : tensor Λ T ⋙ c.model.T ≅ (c.model.T.prod c.model.T) ⋙ tensor Λ' T,
      TensorSectionCondition a T c b barB ∧ SectionTensorNormalized a T c barB := by
  obtain ⟨barB, hbarB⟩ := section_tensor_transport_normalized a T c hc b hb
  exact ⟨barB, section_tensor_transport_condition a T c hc b hb barB hbarB, hbarB⟩

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
