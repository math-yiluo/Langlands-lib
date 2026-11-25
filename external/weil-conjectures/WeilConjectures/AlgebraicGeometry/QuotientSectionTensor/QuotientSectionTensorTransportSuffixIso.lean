/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportSuffixData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedRealization
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTotalSquare
import all WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportFormulas

/-! # Invertibility of the common transport comparison map

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

-- Check the scalar counits and tensor localization factors separately.
/-- The section scalar tensor comparison's final map is invertible on flat-term
K-flat representatives. -/
theorem section_tensor_transport_suffix_isIso (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hbarB : SectionTensorNormalized a T c barB) :
    ∀ (P Q : CochainComplex (Modules Λ T) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      IsIso (section_tensor_transport_suffix a T c P Q) := by
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
  let r := totalComparison Λ T P Q
  let rS := totalComparison Λ' T (Fc.obj P) (Fc.obj Q)
  obtain ⟨g, hg, hB⟩ := ht EP EQ hEP.1 hEQ.1 hEP.2 hEQ.2
  have hord := section_tensor_total_scalar_square a T c hc e he P Q g hg
  have hsT := section_scalar_normalization a T c hc (P ⊗ Q)
  have hn := c.model.ε.naturality r.hom
  simp only [Functor.comp_map] at hn
  have : IsIso (totalScalar a T P Q) := total_scalar_isIso a T P Q
  have : IsIso g := by
    have hi : IsIso (o.hom.app (P ⊗ Q) ≫ Bc.map r.hom ≫ g) := by
      rw [← hord]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)
  have hPT : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (P ⊗ Q) :=
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_tensor hP hQ
  have := compute_isIso a T (P ⊗ Q) hPT
  have : IsIso (c.model.ε.app (ERc.obj (P ⊗ Q))) := by
    have hi : IsIso (c.derived.hom.app (DerivedCategory.Q.obj (P ⊗ Q)) ≫
        BD.map (ℓR.hom.app (P ⊗ Q)) ≫ c.model.ε.app (ERc.obj (P ⊗ Q))) := by
      exact iso_of_eq hsT
    exact (isIso_comp_left_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)
  have : IsIso (c.model.ε.app (EP ⊗ EQ)) := by
    have hi : IsIso (BD.map (DerivedCategory.Q.map r.hom) ≫ c.model.ε.app (EP ⊗ EQ)) := by
      exact iso_of_eq hn
    exact (isIso_comp_left_iff _ _).mp hi
  have : IsIso (c.model.ε.app EP) := c.model.computes EP hEP.1
  have : IsIso (c.model.ε.app EQ) := c.model.computes EQ hEQ.1
  have : IsIso qR := (qTensor_spec Λ T).2.1 EP EQ (Or.inl hEP.1)
  have : IsIso (tensorS.map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ))) :=
    map_pair_iso tensorS _ _
  have : IsIso (tensorS.map (Prod.mkHom (BD.map (ℓR.hom.app P))
      (BD.map (ℓR.hom.app Q)))) := map_pair_iso tensorS _ _
  have hB' : barB.hom.app (DerivedCategory.Q.obj EP, DerivedCategory.Q.obj EQ) ≫
      tensorS.map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) ≫ qS =
    BD.map qR ≫ c.model.ε.app (EP ⊗ EQ) ≫ DerivedCategory.Q.map g := hB
  have : IsIso qS := by
    have hi : IsIso (barB.hom.app (DerivedCategory.Q.obj EP, DerivedCategory.Q.obj EQ) ≫
        tensorS.map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) ≫ qS) := by
      exact iso_of_eq hB'
    exact (isIso_comp_left_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)
  let w := tensorS.map (Prod.mkHom (BD.map (ℓR.hom.app P)) (BD.map (ℓR.hom.app Q))) ≫
    tensorS.map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) ≫ qS
  have hw : IsIso w := by dsimp only [w]; infer_instance
  simpa only [section_tensor_transport_suffix, sectionLocalizationComparison,
    Iso.app_hom, w] using hw

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
