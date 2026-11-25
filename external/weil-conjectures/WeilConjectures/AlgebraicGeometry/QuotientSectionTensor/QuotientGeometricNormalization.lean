/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
import all WeilConjectures.AlgebraicGeometry.SectionDerivedTensorNormalization

/-! # Normalization of the specified geometric operations

## References

* Stacks 07A4 and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

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

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem actual_tensor_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.leftDerivedUpperStarTensor Λ f = internalDelta Λ f := by
  have := CondensedRing.upperStar_preservesFlat Λ f
  rw [CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison,
    internalDelta_eq_canonical]

/-- The fixed section comparisons identify the actual geometric tensorator and adjunction. -/
theorem geometric_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    GeometricCondition Λ f := by
  refine ⟨?_, ?_, ?_⟩
  · intro M N
    apply heq_of_eq
    rw [actual_tensor_eq (Λ := Λ) f]
    have h := (section_derived_tensor_normalization Λ f).2.2.1 M N
    let e := (tensorComparison Λ X).app
        ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≪≫
      (tensor Λ X).mapIso (((derivedPullComparison Λ f).app M).prod
        ((derivedPullComparison Λ f).app N))
    have h' := (e.eq_comp_inv).2 h
    simp only [e, Iso.trans_inv, Functor.mapIso_inv, Iso.prod_inv, Iso.app_inv,
      Category.assoc] at h'
    convert h' using 1 <;> rfl
  · exact (sectionDerivedPushpullNormalization Λ f).2.2.2.2.2.2.2.1
  · exact (sectionDerivedPushpullNormalization Λ f).2.2.2.2.2.2.2.2.1

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
