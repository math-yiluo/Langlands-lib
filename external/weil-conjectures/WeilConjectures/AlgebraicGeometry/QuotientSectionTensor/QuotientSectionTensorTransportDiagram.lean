/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportSuffixData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientTensorLocalization
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTotalSquare
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTotalLocalizationPath
import all WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportFormulas

/-! # The section scalar tensor localization diagram

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

-- Paste the remaining tensor naturality and representative faces.
/-- The scalar tensor localization diagram commutes before its common final map
is cancelled. -/
theorem section_tensor_transport_diagram (T : Scheme.{u})
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
          (D a T).obj (DerivedCategory.Q.obj Q)) ≫
        (tensor Λ' T).map (Prod.mkHom (c.derived.hom.app (DerivedCategory.Q.obj P))
          (c.derived.hom.app (DerivedCategory.Q.obj Q))) ≫
        section_tensor_transport_suffix a T c P Q =
      c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        c.model.T.map ((tensorComparison Λ T).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        barB.hom.app ((derivedFunctor Λ T).obj (DerivedCategory.Q.obj P),
          (derivedFunctor Λ T).obj (DerivedCategory.Q.obj Q)) ≫
        section_tensor_transport_suffix a T c P Q := by
  intro P Q hP hQ hPf hQf
  let := CondensedRing.internalScalarMonoidal a T
  have hEP := (section_resolving_iff (Λ := Λ) T P).mp
    ⟨internal_test_of_kflat (Λ := Λ) T P hP, fun i ↦ (hPf i).2⟩
  have hEQ := (section_resolving_iff (Λ := Λ) T Q).mp
    ⟨internal_test_of_kflat (Λ := Λ) T Q hQ, fun i ↦ (hQf i).2⟩
  obtain ⟨e, he, ht⟩ := hbarB
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
  let τS := tensorComparison Λ' T
  let tensorR := ModuleRingedComparison.tensor Λ T
  let tensorS := ModuleRingedComparison.tensor Λ' T
  let qR := (qTensor Λ T).app (EP, EQ)
  let qS := (qTensor Λ' T).app (Bc.obj EP, Bc.obj EQ)
  obtain ⟨g, hg, hB⟩ := ht EP EQ hEP.1 hEQ.1 hEP.2 hEQ.2
  have hord := section_tensor_total_scalar_square a T c hc e he P Q g hg
  have hsP := section_scalar_normalization a T c hc P
  have hsQ := section_scalar_normalization a T c hc Q
  have hfS := CondensedRing.coefficientTensor_localization Λ' T (Fc.obj P) (Fc.obj Q)
  simp only [internalLocalizationTensorMap_app] at hfS
  have htotalPath := section_tensor_total_localization_path a T c hc P Q g hord
  have hbPQ := congrArg ESD.map (hb P Q hP hQ hPf hQf)
  simp only [Functor.map_comp] at hbPQ
  have htτ := tensor_comparison_natural Λ' T (compute a T P) (compute a T Q)
  have hqnat := localization_tensor_natural Λ' T (o.hom.app P) (o.hom.app Q)
  have hleft :
      c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        BD.map (tensorR.map (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))) ≫
        BD.map qR ≫ c.model.ε.app (EP ⊗ EQ) ≫ DerivedCategory.Q.map g =
      ESD.map (b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        τS.hom.app ((D a T).obj (DerivedCategory.Q.obj P),
          (D a T).obj (DerivedCategory.Q.obj Q)) ≫
        tensorS.map (Prod.mkHom (ESD.map (compute a T P)) (ESD.map (compute a T Q))) ≫
        tensorS.map (Prod.mkHom (ℓS.hom.app (Fc.obj P)) (ℓS.hom.app (Fc.obj Q))) ≫
        tensorS.map (Prod.mkHom (DerivedCategory.Q.map (o.hom.app P))
          (DerivedCategory.Q.map (o.hom.app Q))) ≫ qS := by
    exact paste_internal_path htotalPath hbPQ.symm hfS htτ hqnat
  have hpair := map_pair_three tensorS hsP.symm hsQ.symm
  have htnat := barB.hom.naturality (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))
  simp only [Functor.comp_map, Functor.prod_map] at htnat
  have hright :
      c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        BD.map (tensorR.map (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))) ≫
        BD.map qR ≫ c.model.ε.app (EP ⊗ EQ) ≫ DerivedCategory.Q.map g =
      c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        barB.hom.app (ED.obj (DerivedCategory.Q.obj P), ED.obj (DerivedCategory.Q.obj Q)) ≫
        tensorS.map (Prod.mkHom (BD.map (ℓR.hom.app P)) (BD.map (ℓR.hom.app Q))) ≫
        tensorS.map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) ≫ qS := by
    exact paste_section_path hB htnat
  have hchange := congrArg (fun z ↦
    ESD.map (b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      τS.hom.app ((D a T).obj (DerivedCategory.Q.obj P),
        (D a T).obj (DerivedCategory.Q.obj Q)) ≫ z ≫ qS) hpair
  simp only [Category.assoc] at hchange
  have hcomp := hchange.symm.trans (hleft.symm.trans hright)
  simpa only [section_tensor_transport_suffix, sectionLocalizationComparison,
    Iso.app_hom, Category.assoc] using hcomp

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
