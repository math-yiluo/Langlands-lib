/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientTensorLocalization
import all WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportFormulas

/-! # Localizing the total scalar section tensor square

## References

* Stacks, Cohomology on Sites, Tags 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Keep shared functor terms rather than duplicating them during proof cleanup.
set_option cleanup.letToHave false
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

-- Retain the large total tensor maps while pasting the localization faces.
/-- The total scalar square, localized to the derived category and pasted with scalar
normalization, gives the normalized total path. -/
theorem section_tensor_total_localization_path (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (P Q : CochainComplex (Modules Λ T) ℤ)
    (g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj
        ((((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ⊗
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q)) ⟶
      (c.model.E.mapHomologicalComplex (.up ℤ)).obj
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        (c.model.E.mapHomologicalComplex (.up ℤ)).obj
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q))
    (hord :
    let F := (extension a T).mapHomologicalComplex (.up ℤ)
    let ES := (equivalence Λ' T).functor.mapHomologicalComplex (.up ℤ)
    let o := NatIso.mapHomologicalComplex c.ordinary (.up ℤ)
    ES.map (totalScalar a T P Q) ≫ (totalComparison Λ' T (F.obj P) (F.obj Q)).hom ≫
      (o.hom.app P ⊗ₘ o.hom.app Q) =
    o.hom.app (P ⊗ Q) ≫
      (c.model.E.mapHomologicalComplex (.up ℤ)).map (totalComparison Λ T P Q).hom ≫ g) :
    let F := extension a T
    let ER := (equivalence Λ T).functor
    let ES := (equivalence Λ' T).functor
    let ED := derivedFunctor Λ T
    let ESD := derivedFunctor Λ' T
    let BD := c.model.T
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let ERc := ER.mapHomologicalComplex (.up ℤ)
    let ESc := ES.mapHomologicalComplex (.up ℤ)
    let Bc := c.model.E.mapHomologicalComplex (.up ℤ)
    let EP := ERc.obj P
    let EQ := ERc.obj Q
    let o : Fc ⋙ ESc ≅ ERc ⋙ Bc := NatIso.mapHomologicalComplex c.ordinary (.up ℤ)
    let ℓR : DerivedCategory.Q ⋙ ED ≅ ERc ⋙ DerivedCategory.Q :=
      ER.mapDerivedCategoryFactors
    let ℓS : DerivedCategory.Q ⋙ ESD ≅ ESc ⋙ DerivedCategory.Q :=
      ES.mapDerivedCategoryFactors
    let τR := tensorComparison Λ T
    let tensorR := ModuleRingedComparison.tensor Λ T
    let qR := (qTensor Λ T).app (EP, EQ)
    let rS := totalComparison Λ' T (Fc.obj P) (Fc.obj Q)
    c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
      BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      BD.map (tensorR.map (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))) ≫
      BD.map qR ≫ c.model.ε.app (EP ⊗ EQ) ≫ DerivedCategory.Q.map g =
    ESD.map ((D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ≫
      ESD.map (compute a T (P ⊗ Q)) ≫ ESD.map (DerivedCategory.Q.map (totalScalar a T P Q)) ≫
      ℓS.hom.app (Fc.obj P ⊗ Fc.obj Q) ≫ DerivedCategory.Q.map rS.hom ≫
      DerivedCategory.Q.map (o.hom.app P ⊗ₘ o.hom.app Q) := by
  let F := extension a T
  let ER := (equivalence Λ T).functor
  let ES := (equivalence Λ' T).functor
  let ED := derivedFunctor Λ T
  let ESD := derivedFunctor Λ' T
  let BD := c.model.T
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let ERc := ER.mapHomologicalComplex (.up ℤ)
  let ESc := ES.mapHomologicalComplex (.up ℤ)
  let Bc := c.model.E.mapHomologicalComplex (.up ℤ)
  let EP := ERc.obj P
  let EQ := ERc.obj Q
  let o : Fc ⋙ ESc ≅ ERc ⋙ Bc := NatIso.mapHomologicalComplex c.ordinary (.up ℤ)
  let ℓR : DerivedCategory.Q ⋙ ED ≅ ERc ⋙ DerivedCategory.Q :=
    ER.mapDerivedCategoryFactors
  let ℓS : DerivedCategory.Q ⋙ ESD ≅ ESc ⋙ DerivedCategory.Q :=
    ES.mapDerivedCategoryFactors
  let τR := tensorComparison Λ T
  let tensorR := ModuleRingedComparison.tensor Λ T
  let qR := (qTensor Λ T).app (EP, EQ)
  let r := totalComparison Λ T P Q
  let rS := totalComparison Λ' T (Fc.obj P) (Fc.obj Q)
  have hsT := section_scalar_normalization a T c hc (P ⊗ Q)
  have hfR := CondensedRing.coefficientTensor_localization Λ T P Q
  simp only [internalLocalizationTensorMap_app] at hfR
  have hn := c.model.ε.naturality r.hom
  simp only [Functor.comp_map] at hn
  have htot := congrArg DerivedCategory.Q.map hord
  simp only [Functor.map_comp] at htot
  have hpμ := c.derived.hom.naturality (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)
  have hℓδ := ℓS.hom.naturality (totalScalar a T P Q)
  simp only [Functor.comp_map] at hpμ hℓδ
  have hfacR := congrArg BD.map hfR
  simp only [Functor.map_comp] at hfacR
  exact paste_total_path hfacR hn hpμ hsT.symm htot hℓδ

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
