/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorExistsUnique
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarDerivedTensorIdentification
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # The regular scalar unit and the derived tensor constraints

## References

* Stacks 03EL and 07A4
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

/-- The regular scalar unit is invertible, by K-flat computation in degree zero. -/
theorem scalar_regular_unit_isIso (T : Scheme.{u}) :
    IsIso (scalarRegularUnit a T) := by
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  have := scalarModuleFlat Λ T
  have := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  let := CondensedRing.internalScalarMonoidal a T
  have := CondensedRing.internalScalar_preservesFlat a T
  have hcomp : IsIso (compute a T
      ((CochainComplex.singleFunctor _ 0).obj (𝟙_ (Modules Λ T)))) := by
    apply scalar_compute_isIso
    exact (HomotopyCategory.kFlat_quotient_obj_iff _).1
      (ObjectProperty.prop_unit (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat)
  unfold scalarRegularUnit
  apply IsIso.comp_isIso' hcomp
  apply IsIso.comp_isIso'
  · exact (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (extension a T) (.up ℤ) 0).app (𝟙_ (Modules Λ T)))).isIso_hom
  · exact (DerivedCategory.Q.mapIso
      ((HomologicalComplex.single (Modules Λ' T) (.up ℤ) 0).mapIso
        (Functor.Monoidal.εIso (extension a T)).symm)).isIso_hom

private theorem derivedTensor_map_id_left (T : Scheme.{u})
    (U : DerivedCategory (Modules Λ T)) {V W : DerivedCategory (Modules Λ T)}
    (g : V ⟶ W) :
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T)).map
      (Prod.mkHom (𝟙 U) g) = U ◁ g := by
  change (𝟙 U ▷ V) ≫ (U ◁ g) = U ◁ g
  rw [id_whiskerRight, Category.id_comp]

private theorem derivedTensor_map_id_right (T : Scheme.{u})
    {U V : DerivedCategory (Modules Λ T)} (f : U ⟶ V)
    (W : DerivedCategory (Modules Λ T)) :
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T)).map
      (Prod.mkHom f (𝟙 W)) = f ▷ W := by
  change (f ▷ W) ≫ (V ◁ 𝟙 W) = f ▷ W
  rw [whiskerLeft_id, Category.comp_id]

/-- The normalized tensorator preserves the actual regular scalar unit and constraints. -/
theorem scalar_unit_constraints (T : Scheme.{u}) (b : TensorIso a T)
    (hb : TensorNormalized a T b) : UnitCondition a T b := by
  have hbc := normalized_tensor_eq_canonical a T b hb
  subst b
  let : (D a T).OplaxMonoidal := scalarDerivedOplax a T
  have hderived : IsIso (derivedScalarUnit a T) := by
    rw [← scalarDerivedOplax_η a T]
    exact scalarDerivedOplax_η_isIso a T
  refine ⟨scalar_regular_unit_isIso a T, hderived, ?_⟩
  unfold TensorConstraintCondition
  refine ⟨?_, ?_, ?_⟩
  · intro M N P
    have h := Functor.OplaxMonoidal.associativity (D a T) M N P
    erw [scalarDerivedOplax_δ, scalarDerivedOplax_δ,
      scalarDerivedOplax_δ, scalarDerivedOplax_δ] at h
    erw [derivedTensor_map_id_left, derivedTensor_map_id_right]
    convert h.symm using 1 <;> rfl
  · intro M
    have h := Functor.OplaxMonoidal.left_unitality_hom (D a T) M
    erw [scalarDerivedOplax_δ, scalarDerivedOplax_η] at h
    erw [derivedTensor_map_id_right]
    convert h using 1
  · intro M
    have h := Functor.OplaxMonoidal.right_unitality_hom (D a T) M
    erw [scalarDerivedOplax_δ, scalarDerivedOplax_η] at h
    erw [derivedTensor_map_id_left]
    convert h using 1

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
