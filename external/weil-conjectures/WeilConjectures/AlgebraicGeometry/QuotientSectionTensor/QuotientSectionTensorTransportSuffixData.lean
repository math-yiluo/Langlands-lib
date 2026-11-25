/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # Flat-term representative conjugation for quotient section tensors

## References

* Stacks, Cohomology on Sites, Tags 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
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
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

attribute [local irreducible] ModuleRingedComparison.tensor tensorComparison qTensor
  totalComparison totalScalar QuotientChange.compute Mod.extendScalars
  CondensedRing.internalScalarMonoidal Mod.monoidalCategoryStruct
  Localization.Monoidal.tensorBifunctor
  HomologicalComplex₂.total Mod.inducingFunctorData
  InternalAbelianSheafModule.sectionModuleEquivalence SheafOfModules.monoidalCategory

/-- The common final map in the section scalar tensor comparison.
Compose the tensor of the two localized section equivalence maps, the tensor of
the scalar localization counits, and the section tensor localization map. Every
factor is the specified existing map; this definition makes no choices. -/
@[irreducible] def section_tensor_transport_suffix (T : Scheme.{u})
    (c : ScalarSectionData a T) (P Q : CochainComplex (Modules Λ T) ℤ) :
    let ERc := (equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)
    let Bc := c.model.E.mapHomologicalComplex (.up ℤ)
    (tensor Λ' T).obj
      (c.model.T.obj ((derivedFunctor Λ T).obj (DerivedCategory.Q.obj P)),
        c.model.T.obj ((derivedFunctor Λ T).obj (DerivedCategory.Q.obj Q))) ⟶
      DerivedCategory.Q.obj (Bc.obj (ERc.obj P) ⊗ Bc.obj (ERc.obj Q)) :=
  let ERc := (equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)
  let Bc := c.model.E.mapHomologicalComplex (.up ℤ)
  (tensor Λ' T).map (Prod.mkHom
      (c.model.T.map (sectionLocalizationComparison Λ T P).hom)
      (c.model.T.map (sectionLocalizationComparison Λ T Q).hom)) ≫
    (tensor Λ' T).map (Prod.mkHom (c.model.ε.app (ERc.obj P))
      (c.model.ε.app (ERc.obj Q))) ≫
    (qTensor Λ' T).app (Bc.obj (ERc.obj P), Bc.obj (ERc.obj Q))

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
