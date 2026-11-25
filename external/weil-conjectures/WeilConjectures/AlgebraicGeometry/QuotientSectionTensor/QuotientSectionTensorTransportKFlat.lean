/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportDiagram
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportSuffixIso
import all WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportFormulas

/-! # Flat-term representative conjugation for quotient section tensors

## References

* Stacks 06YY, 07A4 and 07A6
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

-- Paste the localization diagram with its functors retained.
/-- The conjugation equation on flat-term K-flat representatives. -/
theorem section_tensor_transport_kflat (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hbarB : SectionTensorNormalized a T c barB) :
    ∀ (P Q : CochainComplex (Modules Λ T) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      (derivedFunctor Λ' T).map (b.hom.app (DerivedCategory.Q.obj P,
          DerivedCategory.Q.obj Q)) ≫
          (tensorComparison Λ' T).hom.app ((D a T).obj (DerivedCategory.Q.obj P),
            (D a T).obj (DerivedCategory.Q.obj Q)) =
        c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
          c.model.T.map ((tensorComparison Λ T).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
          barB.hom.app ((derivedFunctor Λ T).obj (DerivedCategory.Q.obj P),
            (derivedFunctor Λ T).obj (DerivedCategory.Q.obj Q)) ≫
          (tensor Λ' T).map (Prod.mkHom (c.derived.inv.app (DerivedCategory.Q.obj P))
            (c.derived.inv.app (DerivedCategory.Q.obj Q))) := by
  intro P Q hP hQ hPf hQf
  let ED := derivedFunctor Λ T
  let ESD := derivedFunctor Λ' T
  let BD := c.model.T
  let τR := tensorComparison Λ T
  let τS := tensorComparison Λ' T
  let tensorS := ModuleRingedComparison.tensor Λ' T
  have h := section_tensor_transport_diagram a T c hc b hb barB hbarB P Q hP hQ hPf hQf
  have := section_tensor_transport_suffix_isIso a T c hc barB hbarB P Q hP hQ hPf hQf
  have hcore :
      ESD.map (b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        τS.hom.app ((D a T).obj (DerivedCategory.Q.obj P),
          (D a T).obj (DerivedCategory.Q.obj Q)) ≫
        tensorS.map (Prod.mkHom (c.derived.hom.app (DerivedCategory.Q.obj P))
          (c.derived.hom.app (DerivedCategory.Q.obj Q))) =
      c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        barB.hom.app (ED.obj (DerivedCategory.Q.obj P), ED.obj (DerivedCategory.Q.obj Q)) := by
    apply (cancel_mono (section_tensor_transport_suffix a T c P Q)).mp
    simpa only [Category.assoc] using h
  simpa only [Category.assoc, Iso.app_inv] using
    pair_conjugation tensorS (c.derived.app (DerivedCategory.Q.obj P))
      (c.derived.app (DerivedCategory.Q.obj Q)) hcore

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
