/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationTensorComplex
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

set_option linter.privateModule false

/-! # Direct finite-coefficient derived tensor comparison

Source: Stacks Project, Tags 06YS and 06YU, and the finite coefficient site comparison.
(blueprint: lem-pur-finite-intrinsic-direct-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory

namespace AlgebraicGeometry.ProEtale

private local instance siteSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt

private local instance fixedCountableColimits (A : Type u) [CommRing A] (T : Scheme.{u}) :
    HasColimitsOfSize.{0, 0}
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) := by
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ T
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
    IsGrothendieckAbelian.hasColimits _
  exact hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _

private local instance fixedTensorTotal (A : Type u) [CommRing A] (T : Scheme.{u})
    (V W : CochainComplex
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) :
    HomologicalComplex.HasMapBifunctor V W (curriedTensor _) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _ (fixedCountableColimits A T) _ _) _

attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

-- The comparison below uses only the finite coefficient realization and K-flat models.
-- It never constructs an internal Hom or a tower of coefficient changes.
private theorem realization_acyclic_iff
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsEquivalence] (K : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic ↔ K.Acyclic := by
  constructor
  · intro h i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (h i)
    have hz' : IsZero (F.obj (K.homology i)) :=
      hz.of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K).symm
    apply (IsZero.iff_id_eq_zero _).2
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hz'
  · intro h i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    exact (F.map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1
      (h i))).of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K)

set_option synthInstance.maxSize 4096 in
private theorem intrinsic_flat_representative (A : Type u) [CommRing A] (T : Scheme.{u})
    (K : proEtaleDerivedCategory T A) :
    ∃ P : (SheafOfModules.cochainTensorFlatRepresentatives (Scheme.ProEt.topology T)
        (proEtaleConstantRing T A)).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let R := proEtaleConstantRing T A
  obtain ⟨P, p, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (J := Scheme.ProEt.topology T)
      (R := R) (DerivedCategory.Q.objPreimage K)
  have hp : SheafOfModules.cochainTensorFlatRepresentatives (Scheme.ProEt.topology T) R P := by
    refine ⟨hP, fun i ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X i)).symm (hf i)
  let := hq
  exact ⟨⟨P, hp⟩, ⟨asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

-- Check tensor-instance conversions before specializing to the concrete sheaf category.
set_option synthInstance.maxSize 4096 in
private theorem native_tensor_model_iso.{w, v, z}
    (C : Type z) [Category.{v} C] [Abelian C] [hGv : IsGrothendieckAbelian.{v} C]
    [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]
    (P N : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    letI := DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory.{w, v, z} C
    Nonempty (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (curriedTensor _))) := by
  unfold DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  exact ⟨@DerivedCategory.QObjTensorQObjIsoOfKFlatLeft.{w, v, z} C _ _ hGv
    _ _ _ _ _ _ P N hP⟩

-- The quotient/tensor conversion is inexpensive with an abstract coefficient category.
private theorem kFlat_of_tensor_acyclic.{v, z}
    (C : Type z) [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasColimitsOfSize.{0, 0} C] (P : CochainComplex C ℤ)
    (hP : ∀ V : CochainComplex C ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro V hV
  obtain ⟨V, rfl⟩ := V.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hV
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor V P (curriedTensor C))).2 (hP V hV)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

set_option synthInstance.maxSize 4096 in
private theorem realization_kFlat (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (P : (SheafOfModules.cochainTensorFlatRepresentatives (Scheme.ProEt.topology T)
      (proEtaleConstantRing T A)).FullSubcategory)
    (P' : CochainComplex
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ)
    (eP : ((ProEtale.finiteCoefficientIntrinsicRealization T A).mapHomologicalComplex
      (.up ℤ)).obj P' ≅ P.obj) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P' := by
  let R := proEtaleConstantRing T A
  let F := ProEtale.finiteCoefficientIntrinsicRealization T A
  let : F.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  let FC := F.mapHomologicalComplex (.up ℤ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  apply kFlat_of_tensor_acyclic _ P'
  intro V hV
  apply (realization_acyclic_iff F _).1
  obtain ⟨c⟩ := ProEtale.intrinsic_realization_tensor_complex_iso A T V P'
  let d := ((curriedTensor _).map₂CochainComplex.obj (FC.obj V)).mapIso eP
  intro i
  exact (P.property.1 (FC.obj V) ((realization_acyclic_iff F V).2 hV) i).of_iso
    (c ≪≫ d).symm

set_option synthInstance.maxSize 4096 in
private theorem realization_tensor (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (K L : DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    Nonempty ((SheafOfModules.siteDerivedTensorIndependentCoefficients (Scheme.ProEt.topology T)
        (proEtaleConstantRing T A)).obj
      ((ProEtale.finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj K,
        (ProEtale.finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj L) ≅
      (ProEtale.finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj (K ⊗ L)) := by
  let R := proEtaleConstantRing T A
  let F := ProEtale.finiteCoefficientIntrinsicRealization T A
  let : F.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  let FC := F.mapHomologicalComplex (.up ℤ)
  let E := F.asEquivalence.mapHomologicalComplex (.up ℤ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  obtain ⟨P, ⟨p⟩⟩ := intrinsic_flat_representative A T (F.mapDerivedCategory.obj K)
  obtain ⟨N, ⟨n⟩⟩ := intrinsic_flat_representative A T (F.mapDerivedCategory.obj L)
  let P' := E.inverse.obj P.obj
  let N' := E.inverse.obj N.obj
  let eP : FC.obj P' ≅ P.obj := E.counitIso.app P.obj
  let eN : FC.obj N' ≅ N.obj := E.counitIso.app N.obj
  have hk := realization_kFlat A T P P' eP
  let ek : DerivedCategory.Q.obj P' ≅ K := F.mapDerivedCategory.preimageIso
    (F.mapDerivedCategoryFactors.app P' ≪≫ DerivedCategory.Q.mapIso eP ≪≫ p)
  let el : DerivedCategory.Q.obj N' ≅ L := F.mapDerivedCategory.preimageIso
    (F.mapDerivedCategoryFactors.app N' ≪≫ DerivedCategory.Q.mapIso eN ≪≫ n)
  obtain ⟨c⟩ := ProEtale.intrinsic_realization_tensor_complex_iso A T P' N'
  let d := (Functor.uncurry.obj (curriedTensor _).map₂CochainComplex).mapIso
    (Iso.prod eP eN)
  obtain ⟨r, _, _, _⟩ :=
    SheafOfModules.cochain_tensor_model_rigidity.{u + 1, u, u + 1, u + 2, 0, 0}
    (Scheme.ProEt.topology T) R
  let t := SheafOfModules.siteDerivedTensorIndependentCoefficients (Scheme.ProEt.topology T) R
  obtain ⟨q⟩ := native_tensor_model_iso _ P' N' hk
  exact ⟨t.mapIso (Iso.prod p.symm n.symm) ≪≫ (r.app (P, N)).symm ≪≫
    DerivedCategory.Q.mapIso (c ≪≫ d).symm ≪≫
    (F.mapDerivedCategoryFactors.app _).symm ≪≫
    F.mapDerivedCategory.mapIso
      (q.symm ≪≫ tensorIso ek el)⟩

set_option synthInstance.maxSize 4096 in
private def comparison_tensor (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (K L : Etale.DerivedCategoryModule (ULift.{u + 1} A) T) :
    (SheafOfModules.siteDerivedTensorIndependentCoefficients (Scheme.ProEt.topology T)
        (proEtaleConstantRing T A)).obj
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).obj K,
        (ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).obj L) ≅
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).obj (K ⊗ L) := by
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let F := ProEtale.finiteCoefficientIntrinsicRealization T A
  let e := (Functor.mapDerivedCategoryCompIso ν F).symm
  let t := SheafOfModules.siteDerivedTensorIndependentCoefficients (Scheme.ProEt.topology T)
    (proEtaleConstantRing T A)
  exact t.mapIso (Iso.prod (e.app K) (e.app L)) ≪≫
    (realization_tensor A T (ν.mapDerivedCategory.obj K) (ν.mapDerivedCategory.obj L)).some ≪≫
    F.mapDerivedCategory.mapIso
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) K).app L).symm ≪≫ (e.app (K ⊗ L)).symm

end AlgebraicGeometry.ProEtale
