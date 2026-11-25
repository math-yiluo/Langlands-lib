/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalLeft
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalRight

/-! # Pasting the two scalar tensor evaluations

## References

* Stacks 06YY and 07A4, the scalar tensor localization square
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

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

/-- Paste the two internal-image evaluations and cancel the invertible input. -/
theorem section_tensor_transport_internal_counit (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    [PreservesColimitsOfSize.{0, 0} c.model.E]
    (hbarB : TensorSectionCondition a T c b barB)
    (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
        (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
          (curriedTensor (modules Λ' T)))
    (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
      (n : N.val.obj W) (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
          (sectionScalarElement a T c (M ⊗ N) W
            (sectionPureTensor Λ T M N W m n) s) =
        sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
          (sectionScalarElement a T c M W m 1)
          (sectionScalarElement a T c N W n s)) :
    ∀ P Q : CochainComplex (Modules Λ T) ℤ,
      let EP := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P
      let EQ := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) EP →
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) EQ →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (EP.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (EQ.X i)) →
      barB.hom.app (DerivedCategory.Q.obj EP, DerivedCategory.Q.obj EQ) ≫
          (tensor Λ' T).map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) ≫
          (qTensor Λ' T).app
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj EP,
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj EQ) =
        c.model.T.map ((qTensor Λ T).app (EP, EQ)) ≫
          c.model.ε.app ((totalTensor Λ T).obj (EP, EQ)) ≫
          DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorComparison e (.up ℤ) EP EQ) := by
  intro P Q
  dsimp only
  intro hP hQ hfP hfQ
  have hl := section_tensor_transport_internal_left a T c hc b hb barB hbarB
    P Q hP hQ hfP hfQ
  have hr := section_tensor_transport_internal_right a T c hc e he P Q
  have hj : IsIso (scalarTensorSectionInput a T c P Q) := by
    let : IsIso (Prod.mkHom
        (sectionLocalizationComparison Λ T P).hom
        (sectionLocalizationComparison Λ T Q).hom) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    unfold scalarTensorSectionInput
    infer_instance
  apply (cancel_epi (scalarTensorSectionInput a T c P Q)).mp
  simpa only [Category.assoc] using hl.trans hr.symm

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
