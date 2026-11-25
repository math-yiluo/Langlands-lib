/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalData
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportFormulas
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalLeftCore
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Derived-side scalar tensor evaluation

## References

* Stacks Project, Tags 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u u₁ v₁
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

/-- Evaluate the derived tensor side on internal resolving complexes. -/
private theorem kflat_from_acyclic_test_local
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ)
    (hP : ∀ A : CochainComplex C ℤ, A.Acyclic →
      (CochainComplex.mapBifunctor A P (curriedTensor C)).Acyclic) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff, HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro A hA
  obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hA
  have h := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
    (hP A hA)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) h, h⟩

-- The derived-category equivalence and tensor comparison require a large elaboration budget.
theorem section_tensor_transport_internal_left (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hbarB : TensorSectionCondition a T c b barB) :
    ∀ P Q : CochainComplex (Modules Λ T) ℤ,
      let EP := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P
      let EQ := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) EP →
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) EQ →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (EP.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (EQ.X i)) →
      scalarTensorSectionInput a T c P Q ≫
        barB.hom.app (DerivedCategory.Q.obj EP, DerivedCategory.Q.obj EQ) ≫
          (tensor Λ' T).map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) ≫
          (qTensor Λ' T).app
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj EP,
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj EQ) =
        scalarTensorSectionPath a T c P Q := by
  intro P Q
  dsimp only
  intro hP hQ hfP hfQ
  let E := (equivalence Λ T).functor
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
  let EQ := (E.mapHomologicalComplex (.up ℤ)).obj Q
  have hcmp := (InternalAbelianSheafModule.internal_section_tensor_comparison
    (Scheme.ProEt.topology T) (condensedRingObj Λ T)).2.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.2
  have htestP : ∀ A : CochainComplex (internalModules Λ T) ℤ, A.Acyclic →
      (CochainComplex.mapBifunctor A P (curriedTensor _)).Acyclic :=
    hcmp P |>.mpr hP
  have htestQ : ∀ A : CochainComplex (internalModules Λ T) ℤ, A.Acyclic →
      (CochainComplex.mapBifunctor A Q (curriedTensor _)).Acyclic :=
    hcmp Q |>.mpr hQ
  have hKP := kflat_from_acyclic_test_local P htestP
  have hKQ := kflat_from_acyclic_test_local Q htestQ
  have hflatP : ∀ i : ℤ, ObjectProperty.flat (P.X i) := fun i ↦
    (CategoryTheory.InternalAbelianSheafModule.flat_iff_sectionModule
      (Scheme.ProEt.topology T) (condensedRingObj Λ T) (P.X i)).2 (hfP i)
  have hflatQ : ∀ i : ℤ, ObjectProperty.flat (Q.X i) := fun i ↦
    (CategoryTheory.InternalAbelianSheafModule.flat_iff_sectionModule
      (Scheme.ProEt.topology T) (condensedRingObj Λ T) (Q.X i)).2 (hfQ i)
  have hbn := hb P Q hKP hKQ hflatP hflatQ
  have hcn := section_scalar_normalization a T c hc (P ⊗ Q)
  have hqnorm := (section_derived_tensor_normalization
    (Λ := Λ) (X := T) (Y := T) (f := 𝟙 T)).1 T |>.1 P Q
  exact section_tensor_transport_internal_left_core a T c hc b hb barB hbarB P Q hbn hcn hqnorm

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
