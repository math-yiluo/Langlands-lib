/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # The scalar adjunction of the quotient normalization

## References

* Stacks Project, Tags 03EL and 06YY
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryNatIso
  completedReductionCoefficient completedReductionDerivedNormalization

private theorem counit_eq
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex B ℤ) :
    reductionComplexCounit F L ε K =
      ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) := by
  have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have hi : (DerivedCategory.quotientCompQhIso B).inv.app K = 𝟙 _ := rfl
  have hh : (DerivedCategory.quotientCompQhIso C).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  simp only [reductionComplexCounit, hi, hh, hid]
  erw [L.map_id, (DerivedCategory.Qh (C := C)).map_id]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id]

private theorem canonicalTranspose (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ∀ (P : CochainComplex (reductionModules T R) ℤ)
      (K : CochainComplex (reductionModules T S) ℤ)
      (f : ((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    (pbcDerivedScalarAdjunction a).homEquiv _ _
      (reductionScalarComplexCounit T a P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          (((pbcScalarAdjunction a).mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
            (reductionRestrict T a).mapDerivedCategoryFactors.inv.app K := by
  obtain ⟨ad, had⟩ := SheafOfModules.sheafRingDerivedHomComparison.{u + 2, u + 1, u + 1, u} a
    (reductionChange T a) (reductionChange_obj_eq T a) (reductionChange_map_eq T a)
    (pbcScalarAdjunction a) (reductionDerivedChange T a) (reductionDerivedCounit T a)
    (reductionDerivedUniversal T a)
  have hc := CategoryTheory.adjunction_cochain_transpose
    (reductionChange T a) (reductionRestrict T a) (pbcScalarAdjunction a)
    (reductionDerivedChange T a)
    (complexCounitNat (reductionChange T a) (reductionDerivedChange T a)
      (reductionDerivedCounit T a)) (reductionDerivedCounit T a)
    (fun P ↦ by
      change _ ≫ 𝟙 _ = (reductionDerivedChange T a).map (𝟙 _) ≫ _
      erw [(reductionDerivedChange T a).map_id, Category.id_comp, Category.comp_id]
      simpa only [complexCounitNat_app] using
        (counit_eq (reductionChange T a) (reductionDerivedChange T a)
          (reductionDerivedCounit T a) P).symm) ad had
  have he : ad = pbcDerivedScalarAdjunction a := by
    unfold pbcDerivedScalarAdjunction
    with_unfolding_all
      apply (pbcDerivedScalarAdjunction_exists a).unique ?_
        (pbcDerivedScalarAdjunction_exists a).exists.choose_spec
      intro P hP
      have hu := hc P (((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
      erw [DerivedCategory.Q.map_id, Category.comp_id, Adjunction.homEquiv_id] at hu
      have hv := congrArg (fun f ↦ f ≫ (reductionRestrict T a).mapDerivedCategoryFactors.hom.app
        (((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P)) hu
      simp only [Category.assoc, Iso.inv_hom_id_app] at hv
      change ad.unit.app _ ≫ _ ≫ _ = _
      simp only [complexCounitNat_app, Adjunction.homEquiv_unit] at hv
      have hv' := hv.trans (Category.comp_id _)
      exact (Category.assoc _ _ _).symm.trans hv'
  rw [he] at hc
  intro P K f
  have hh := hc P K f
  erw [complexCounitNat_app] at hh
  with_unfolding_all exact hh

private theorem scalarComposition_rep (T : Scheme.{u})
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ) :
    ((((pbcDerivedScalarAdjunction φ).comp (pbcDerivedScalarAdjunction ψ)).ofNatIsoRight
        (pbcDerivedRestrictComp φ ψ χ h)).leftAdjointUniq
          (pbcDerivedScalarAdjunction χ)).hom.app (DerivedCategory.Q.obj P) ≫
        reductionScalarComplexCounit T χ P =
      (reductionDerivedChange T ψ).map (reductionScalarComplexCounit T φ P) ≫
        reductionScalarComplexCounit T ψ ((reductionChangeComplex T φ).obj P) ≫
        DerivedCategory.Q.map (reductionBalance T φ ψ χ h P) := by
  let ac := (pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)
  let bc := (pbcScalarAdjunction ψ).mapHomologicalComplex (.up ℤ)
  let dc := (pbcScalarAdjunction χ).mapHomologicalComplex (.up ℤ)
  let η := pbcRestrictComp φ ψ χ h
  let ηc := Functor.mapHomologicalComplexCompIso η (.up ℤ)
  let δ := pbcDerivedRestrictComp φ ψ χ h
  let εφ := complexCounitNat (reductionChange T φ) (reductionDerivedChange T φ)
    (reductionDerivedCounit T φ)
  let εψ := complexCounitNat (reductionChange T ψ) (reductionDerivedChange T ψ)
    (reductionDerivedCounit T ψ)
  have hn (Q : CochainComplex (reductionModules T R) ℤ) :
      (ac.comp bc).homEquiv _ _ (reductionBalance T φ ψ χ h Q) ≫
        ηc.hom.app ((reductionChangeComplex T χ).obj Q) = dc.unit.app Q := by
    apply HomologicalComplex.hom_ext
    intro i
    ext U x
    change ((η.hom.app ((reductionChange T χ).obj (Q.X i))).val.app U)
      (((reductionBalance T φ ψ χ h Q).f i).val.app U
        (((pbcScalarAdjunction ψ).unit.app ((reductionChange T φ).obj (Q.X i))).val.app U
          (((pbcScalarAdjunction φ).unit.app (Q.X i)).val.app U x))) =
      ((pbcScalarAdjunction χ).unit.app (Q.X i)).val.app U x
    dsimp only [η, pbcRestrictComp]
    erw [(pbcRestrictComp_exists φ ψ χ h).exists.choose_spec]
    erw [(pbcScalarAdjunction_exists φ).exists.choose_spec,
      (pbcScalarAdjunction_exists ψ).exists.choose_spec,
      (pbcScalarAdjunction_exists χ).exists.choose_spec]
    change ((reductionBalance T φ ψ χ h Q).f i).val.app U
      (reductionTensorSection T ψ ((reductionChange T φ).obj (Q.X i)) U 1
        (reductionTensorSection T φ (Q.X i) U 1 x)) =
      reductionTensorSection T χ (Q.X i) U 1 x
    rw [reductionBalance_tmul, map_one, one_mul]
  have hcomp := normalizedAdjunction_composition ac bc
    (pbcDerivedScalarAdjunction φ) (pbcDerivedScalarAdjunction ψ)
    εφ εψ (reductionRestrict T φ).mapDerivedCategoryFactors.inv
    (reductionRestrict T ψ).mapDerivedCategoryFactors.inv
    (fun Q K g ↦ by
      simpa only [εφ, ac, complexCounitNat_app] using canonicalTranspose T φ Q K g)
    (fun Q K g ↦ by
      simpa only [εψ, bc, complexCounitNat_app] using canonicalTranspose T ψ Q K g)
  have hρ (Q : CochainComplex (reductionModules T B) ℤ) :
      (reductionRestrict T φ).mapDerivedCategoryFactors.inv.app
          (((reductionRestrict T ψ).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        (reductionDerivedRestrict T φ).map
          ((reductionRestrict T ψ).mapDerivedCategoryFactors.inv.app Q) ≫
        δ.hom.app (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map (ηc.hom.app Q) ≫
        (reductionRestrict T χ).mapDerivedCategoryFactors.inv.app Q :=
    Functor.exactDerivedRestrictionComposition_inv_factors
      (reductionRestrict T ψ) (reductionRestrict T φ) (reductionRestrict T χ) η Q
  have hh := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q) (ac.comp bc) dc
    ((pbcDerivedScalarAdjunction φ).comp (pbcDerivedScalarAdjunction ψ))
    (pbcDerivedScalarAdjunction χ)
    (fun Q ↦ (reductionDerivedChange T ψ).map (reductionScalarComplexCounit T φ Q) ≫
      reductionScalarComplexCounit T ψ ((reductionChangeComplex T φ).obj Q))
    (reductionScalarComplexCounit T χ)
    (fun Q ↦ (reductionRestrict T φ).mapDerivedCategoryFactors.inv.app
        (((reductionRestrict T ψ).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (reductionDerivedRestrict T φ).map
        ((reductionRestrict T ψ).mapDerivedCategoryFactors.inv.app Q))
    (reductionRestrict T χ).mapDerivedCategoryFactors.inv.app
    (by
      intros Q K g
      simpa only [εφ, εψ, complexCounitNat_app, reductionScalarComplexCounit,
        reductionChangeComplex, pbcDerivedExtend, pbcExtend, pbcDerivedRestrict,
        pbcRestrict, reductionDerivedRestrict, reductionRestrict,
        proEtaleRingRestrictScalars, Category.assoc] using hcomp Q K g)
    (canonicalTranspose T χ) ηc δ
    (reductionBalance T φ ψ χ h) hn
    (by intro Q; simpa only [Category.assoc] using hρ Q) P
  simpa only [δ, Category.assoc] using hh

end AlgebraicGeometry.Scheme
