/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarExchange
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.SixFunctors.OrdinaryFieldRealization.FieldStageOrdinaryRealization
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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

import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement

import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore

import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Monoidal.Preadditive

import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

import WeilConjectures.Algebra.Homology.SmoothPurity.RestrictedScalarCohomologyLocalConstancy

import all WeilConjectures.AlgebraicGeometry.Finite.FiniteTensorConstructibleCohomology

import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # Derived scalar extension on the small pro-etale site

The underlying functor is the canonical K-flat derived extension of scalars along a
map of constant coefficient rings.  The accompanying statements record its exactness,
finite constructibility and Tor-amplitude preservation, Tate-line scalar extension,
and the canonical associativity comparisons.

## References

* Stacks 06YS, 06YY
* Stacks 094H, 06YY
* Stacks 06YQ
* Stacks 0G7E, 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Derived extension of scalars on the ordinary constant-ring pro-etale categories.
The target category carries its action through the right tensor factor. -/
noncomputable def scalarExtensionFunctor {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory T B :=
  scalarExtension f T

/-- The actual universal counit on a complex, rather than a chosen model comparison. -/
def scalarExtensionFunctorCounit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :=
  reductionScalarComplexCounit T (proEtaleConstantRingMap (T := T) f) P

/-- K-flat computation, including the functor and its target-ring tensor action. -/
theorem scalarExtensionFunctor_kflat_representation
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T A) P) :
    IsIso (scalarExtensionFunctorCounit f T P) := by
  exact scalarCounit_isIso T (proEtaleConstantRingMap (T := T) f) P hP

/-- The canonical formula S_f(Q(P)) ≅ Q(P tensor B), on every K-flat representative. -/
def scalarExtensionFunctorKFlatIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T A) P) :
    (scalarExtensionFunctor f T).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) :=
  @asIso _ _ _ _ (scalarExtensionFunctorCounit f T P)
    (scalarExtensionFunctor_kflat_representation f T P hP)

section ConstructibilityProof
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
private theorem scalarExtensionSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance] scalarExtensionSmall
open MonoidalCategory

attribute [local irreducible] SheafOfModules.monoidalCategory

section AbstractTensor
universe cv cu cw

private theorem scalarExtension_abstract_tensor_comparison
    {C : Type cu} [CategoryTheory.Category.{cv} C] [Abelian C]
  [IsGrothendieckAbelian.{cv} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [HasDerivedCategory.{cw} C]
  [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ)
    (hP : ∀ V : CochainComplex C ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic)
    (K : DerivedCategory C) (e : DerivedCategory.Q.obj P ≅ K) (M : C) :
    Nonempty (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P
      ((HomologicalComplex.single C (.up ℤ) 0).obj M) (curriedTensor C)) ≅
        K ⊗ (DerivedCategory.singleFunctor C 0).obj M) := by
  have hk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro V hV
    obtain ⟨V, rfl⟩ := V.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hV
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor V P (curriedTensor C))).2 (hP V hV)
    refine ⟨?_, hr⟩
    exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr
  exact ⟨DerivedCategory.Q.mapIso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P) ≪≫
    (DerivedCategory.QObjTensorSingleFunctorObjIso P hk M).symm ≪≫
      tensorIso e (Iso.refl _)⟩
private theorem scalarExtension_abstract_tor_iff
    {C : Type cu} [CategoryTheory.Category.{cv} C] [Abelian C]
  [IsGrothendieckAbelian.{cv} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [HasDerivedCategory.{cw} C]
  [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) (a b : ℤ) (hab : a ≤ b)
    (hRes : ∀ L : CochainComplex C ℤ,
      ∃ (P : CochainComplex C ℤ) (f : P ⟶ L), QuasiIso f ∧
        ∀ V : CochainComplex C ℤ, V.Acyclic →
          (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic) :
    (a ≤ b ∧ ∀ (L P : CochainComplex C ℤ), Nonempty (DerivedCategory.Q.obj L ≅ K) →
      ∀ (f : P ⟶ L), QuasiIso f →
        (∀ V : CochainComplex C ℤ, V.Acyclic →
          (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic) →
      ∀ (M : C) (i : ℤ), i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor C i).obj
          (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P
            ((HomologicalComplex.single C (.up ℤ) 0).obj M) (curriedTensor C))))) ↔
      DerivedCategory.torAmplitudeIn C a b K := by
  have compare (L P : CochainComplex C ℤ) (eL : DerivedCategory.Q.obj L ≅ K)
      (f : P ⟶ L) (hf : QuasiIso f)
      (hP : ∀ V : CochainComplex C ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V P (curriedTensor C)).Acyclic) (M : C) :
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) (curriedTensor C)) ≅
        K ⊗ (DerivedCategory.singleFunctor C 0).obj M := by
    have : QuasiIso f := hf
    exact (scalarExtension_abstract_tensor_comparison P hP K
      (asIso (DerivedCategory.Q.map f) ≪≫ eL) M).some
  constructor
  · intro h M
    let L := DerivedCategory.Q.objPreimage K
    let eL := DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨P, f, hf, hP⟩ := hRes L
    refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_, (DerivedCategory.isLE_iff _ b).2 ?_⟩
    · intro i hi
      exact (h.2 L P ⟨eL⟩ f hf hP M i (Or.inl hi)).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso (compare L P eL f hf hP M)).symm
    · intro i hi
      exact (h.2 L P ⟨eL⟩ f hf hP M i (Or.inr hi)).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso (compare L P eL f hf hP M)).symm
  · intro h
    refine ⟨hab, ?_⟩
    intro L P heL f hf hP M i hi
    obtain ⟨eL⟩ := heL
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor C i).mapIso
      (compare L P eL f hf hP M))
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ a).1 (h M).1 i hi
    · exact (DerivedCategory.isLE_iff _ b).1 (h M).2 i hi

end AbstractTensor

private theorem scalarExtension_tor_flat_model
    (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (a b : ℤ) (hab : a ≤ b) :
    HasProEtaleTorAmplitude T A K a b ↔
      ∃ P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ,
        (∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := ProEt.topology T) (R := proEtaleConstantRing T A) (P.X i)) ∧
        (∀ i, i < a ∨ b < i → IsZero (P.X i)) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  classical
  let R := proEtaleConstantRing T A
  let C := proEtaleRingModules T R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have : IsGrothendieckAbelian.{u + 1} C :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology T) _
  have : ∀ X Y : GradedObject ℤ C, GradedObject.HasTensor X Y := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ C,
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ C,
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  have : ∀ X Y Z W : GradedObject ℤ C,
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  have : DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ)) := by infer_instance
  have htor : HasProEtaleTorAmplitude T A K a b ↔
      DerivedCategory.torAmplitudeIn C a b K := by
    apply scalarExtension_abstract_tor_iff K a b hab
    intro L
    obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
    exact ⟨P, f, hf, hP⟩
  rw [htor, DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat]
  have hflat (M : C) : CategoryTheory.ObjectProperty.flat M ↔
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := R) M := by
    refine ⟨fun h ↦ ?_, SheafOfModules.flat_to_cat R M⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M).symm h.2
  constructor
  · rintro ⟨P, hge, hle, hP, ⟨e⟩⟩
    refine ⟨P, fun i ↦ (hflat _).1 (hP i), ?_, ⟨e.symm⟩⟩
    intro i hi
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  · rintro ⟨P, hP, hb, ⟨e⟩⟩
    have hge : P.IsStrictlyGE a :=
      (CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi ↦ hb i (Or.inl hi))
    have hle : P.IsStrictlyLE b :=
      (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦ hb i (Or.inr hi))
    exact ⟨P, hge, hle, fun i ↦ (hflat _).2 (hP i), ⟨e.symm⟩⟩

private theorem scalarExtension_tor
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A)
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude T A K a b) :
    HasProEtaleTorAmplitude T B ((scalarExtensionFunctor f T).obj K) a b := by
  classical
  let R := proEtaleConstantRing T A
  let S := proEtaleConstantRing T B
  let φ := proEtaleConstantRingMap (T := T) f
  let E := reductionChange T φ
  obtain ⟨P, hf, hb, ⟨e⟩⟩ := (scalarExtension_tor_flat_model T A K a b hTor.1).mp hTor
  have : P.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦ hb i (Or.inr hi))
  have hP := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P b hf
  have hext := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    φ P E (reductionChange_obj_eq T φ) (fun g ↦ reductionChange_map_eq T φ g) hP
      (fun i ↦ (SheafOfModules.flat_to_cat R (P.X i) (hf i)).2)
  let Q := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hQ : ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := S) (Q.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso S (Q.X i)).symm (hext.2 i)
  have hP' : CochainComplex.IsAcyclicTensorKFlat (R := R) P :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP
  let c : (scalarExtensionFunctor f T).obj K ≅ DerivedCategory.Q.obj Q :=
    (scalarExtensionFunctor f T).mapIso e ≪≫ scalarExtensionFunctorKFlatIso f T P hP'
  apply (scalarExtension_tor_flat_model T B _ a b hTor.1).mpr
  exact ⟨Q, hQ, fun i hi ↦ E.map_isZero (hb i hi), ⟨c⟩⟩

private theorem scalarExtension_bounded_of_tor
    (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (a b : ℤ)
    (hTor : HasProEtaleTorAmplitude T A K a b) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)} := by
  classical
  obtain ⟨P, _, hb, ⟨e⟩⟩ := (scalarExtension_tor_flat_model T A K a b hTor.1).mp hTor
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hout
  have hor : i < a ∨ b < i := by
    change ¬ (a ≤ i ∧ i ≤ b) at hout
    omega
  have hz := (P.sc i).isZero_homology_of_isZero_X₂ (hb i hor)
  exact hi (hz.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P))

private theorem scalarExtension_cochainModelIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u}) :
    Nonempty (scalarExtensionFunctor f T ≅
      SheafOfModules.constantCoefficientScalarExtensionOfUniverses.{u + 1, u, u + 1, u + 2, u + 2}
        (ProEt.topology T)
          ((ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).symm.toRingHom.comp
            (f.comp (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).toRingHom))) := by
  let α := proEtaleConstantRingMap (T := T) f
  let D := Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel α)
  let E := reductionChange T α
  let F := reductionDerivedChange T α
  let ε := reductionDerivedCounit T α
  let c := complexCounitNat E F ε
  have : F.IsLeftDerivedFunctor c
      (HomologicalComplex.quasiIso (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)) :=
    complexCounitNat_kan E F ε
  have : D.T.IsLeftDerivedFunctor D.ε
      (HomologicalComplex.quasiIso (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)) :=
    D.universal
  let e : E ≅ D.E := NatIso.ofComponents
    (fun M ↦ eqToIso ((reductionChange_obj_eq T α M).trans (D.obj_eq M).symm)) (by
      intro M N g
      dsimp only [eqToIso.hom]
      rw [reductionChange_map_eq, D.map_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans])
  let d := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q
  exact ⟨Functor.leftDerivedNatIso F D.T c D.ε
    (HomologicalComplex.quasiIso (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)) d⟩

private theorem scalarExtension_models_finiteLocal
    (S : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses.{u, u} S A
      (fun M ↦ Finite M) L) :
    IsLocallyConstantProEtaleModuleSheaf S A L ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing S A) L) := by
  classical
  obtain ⟨I, U, f, hf, he⟩ := hL
  let B := ULift.{u + 1} A
  let F := (proEtaleModuleRestriction S A).obj L
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage S := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage S at hf
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 S = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    simpa only [hw] using hf
  apply (finiteLocal_iff S A L).mp
  refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := he i
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit S A)
  have ha := proEtaleConstantRingUnit_over_locallyBijective S A (U i)
  have hai : Presheaf.IsLocallyInjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.1
  have has : Presheaf.IsLocallySurjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.2
  let E := ConstantScalarComparison.restriction ((ProEt.topology S).over (U i))
    B (R.over (U i)) a
  have := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology S).over (U i)) B (R.over (U i)) a M
  let e : F.over (U i) ≅ (constantSheaf ((ProEt.topology S).over (U i))
      (ModuleCat.{u + 1} B)).obj M :=
    E.mapIso eM ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology S).over (U i)) B (R.over (U i)) a M)).symm
  have : (ProEt.sliceEquiv S (U i)).inverse.IsDenseSubsite
      (ProEt.topology (U i).left) ((ProEt.topology S).over (U i)) :=
    ProEt.sliceDense S (U i)
  let D := (ProEt.sliceEquiv S (U i)).sheafCongr
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} B)
  let r : D.functor.obj (F.over (U i)) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U i).hom (U i).prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv S (U i)).constantSheafSheafCongrIso
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U i))).app M
  exact ⟨M, (have := hM; Module.Finite.of_finite), ⟨
    (ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F ≪≫
    r.symm ≪≫ D.functor.mapIso e ≪≫ c⟩⟩

private theorem scalarExtension_constructible
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)) :
    ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
          ((scalarExtensionFunctor f T).obj K)) := by
  classical
  let H := fun j : ℤ ↦ (DerivedCategory.homologyFunctor
    (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj K
  obtain ⟨S, hn, hS⟩ := common_stratification hbounded.toFinset T A H
    (fun j _ ↦ hconstructible j)
  have hKb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (H j) := by
    obtain ⟨b, hb⟩ := hbounded.bddAbove
    refine ⟨b, fun j hj ↦ ?_⟩
    by_contra hz
    exact (not_le_of_gt hj) (hb hz)
  have hstratum (i : Fin S.n) (j : ℤ) :
      IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} (S.domain i) A
        (proEtaleConstantModulePullback (S.immersion i) A (H j)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing (S.domain i) A)
          (proEtaleConstantModulePullback (S.immersion i) A (H j))) := by
    by_cases hz : IsZero (H j)
    · have hzero := pullback_isZero (S.immersion i) A (H j) hz
      refine ⟨?_, fun Ω _ _ x ↦ finite_stalk_of_isZero _ A _ hzero x⟩
      obtain ⟨I, U, f, hf, hM⟩ := locallyConstant_of_isZero _ A _ hzero
      exact ⟨I, U, f, hf, fun k ↦ ⟨(hM k).choose, trivial, (hM k).choose_spec⟩⟩
    · obtain ⟨hl, hs⟩ := hS j (hbounded.mem_toFinset.mpr hz) i
      obtain ⟨I, U, f, hf, hM⟩ := hl
      exact ⟨⟨I, U, f, hf, fun k ↦ ⟨(hM k).choose, trivial, (hM k).choose_spec⟩⟩, hs⟩
  intro q
  let D := SheafOfModules.constantCoefficientScalarExtensionOfUniverses
    (ProEt.topology T)
      ((ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).symm.toRingHom.comp
        (f.comp (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).toRingHom))
  have hD : IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) q).obj (D.obj K)) := by
    refine ⟨S, hn, fun i ↦ ?_⟩
    exact scalarExtension_models_finiteLocal (S.domain i) B _
      (restrictedScalarCohomology_finiteLocalModels (S.immersion i) f K hKb
        (hstratum i) q)
  obtain ⟨e⟩ := scalarExtension_cochainModelIso f T
  exact constructibleProEtale_of_iso T B
    ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T B)) q).mapIso
        (e.symm.app K)) hD

end ConstructibilityProof

attribute [local instance] scalarExtensionSmall

/-- Constructibility, boundedness and the identical Tor interval survive arbitrary
finite coefficient extension, including non-flat maps. -/
theorem scalarExtensionFunctor_preserves_constructible_tor
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K))
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude T A K a b) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
        ((scalarExtensionFunctor f T).obj K))} ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
          ((scalarExtensionFunctor f T).obj K))) ∧
    HasProEtaleTorAmplitude T B ((scalarExtensionFunctor f T).obj K) a b := by
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hB
  have ht := scalarExtension_tor f T K a b hTor
  exact ⟨scalarExtension_bounded_of_tor T B _ a b ht,
    scalarExtension_constructible f T K hbounded hconstructible, ht⟩

/-- A line extends by ordinary tensor and remains locally free of rank one. -/
theorem scalarExtensionFunctor_line
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    IsIso (scalarExtensionFunctorCounit f T
      ((HomologicalComplex.single _ (.up ℤ) 0).obj L)) ∧
    SheafOfModules.IsFiniteLocallyFreeOfRank
      ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L) 1 := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := proEtaleConstantRing T A
  let S := proEtaleConstantRing T B
  have : L.IsFiniteLocallyFreeOfRank 1 := hL
  let F := SheafOfModules.siteSheafTensorRight (A := R) L
  let G := SheafOfModules.siteSheafTensorRight (A := R)
    (WeilConjectures.coefficientTwistLine T L (-1))
  obtain ⟨e⟩ := (WeilConjectures.signedLineTensor_equivalence T R L 1).2
  obtain ⟨d⟩ := (WeilConjectures.signedLineTensor_equivalence T R L (-1)).2
  let eqv : proEtaleRingModules T R ≌ proEtaleRingModules T R :=
    CategoryTheory.Equivalence.mk F G e.symm (by
      simpa only [F, G, WeilConjectures.coefficientTwistLine,
        WeilConjectures.coefficientTwistPower, SheafOfModules.scalarTensorPower,
        neg_neg] using d)
  have : PreservesFiniteLimits F := inferInstanceAs (PreservesFiniteLimits eqv.functor)
  have : PreservesFiniteColimits F := inferInstanceAs (PreservesFiniteColimits eqv.functor)
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let collapse := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (MonoidalCategory.curriedTensor (proEtaleRingModules T R)) L ≪≫
      NatIso.mapHomologicalComplex (SheafOfModules.siteSheafTensorRightIso R L).symm (.up ℤ)
  have hk : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := R) ((HomologicalComplex.single _ (.up ℤ) 0).obj L) := by
    intro P hP i
    exact ((hP.map F) i).isZero_homology.of_iso
      (HomologicalComplex.homologyMapIso (collapse.app P) i) |>
        (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
  refine ⟨scalarExtensionFunctor_kflat_representation f T _ hk, ?_⟩
  have : L.IsInvertible := (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).2 hL
  have hext := (SheafOfModules.scalarExtensionDual_localIsomorphism.{u + 1, u, u + 1}
    R S (proEtaleConstantRingMap (T := T) f) L).1
  have : ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L).IsInvertible := by
    rw [proEtaleRingExtension_obj]
    exact hext
  exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
    ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L)).1 inferInstance

/-- The rank-one derived computation as an explicit isomorphism to ordinary scalar tensor. -/
def scalarExtensionFunctorLineIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (T : Scheme.{u})
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    (scalarExtensionFunctor f T).obj ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).obj L) :=
  @asIso _ _ _ _
      (scalarExtensionFunctorCounit f T ((HomologicalComplex.single _ (.up ℤ) 0).obj L))
      (scalarExtensionFunctor_line f T L hL).1 ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)) (.up ℤ) 0).app L)

section TateComparisonProof

-- Keep the tensor and dual APIs abstract during elaboration.
set_option backward.isDefEq.respectTransparency true

section SignedComparisonEvaluation

end SignedComparisonEvaluation

end TateComparisonProof

section TateExponentProof
set_option backward.isDefEq.respectTransparency true


end TateExponentProof

/-- The constant ring maps compose as the specified ring homomorphisms do. -/
theorem scalarExtensionFunctor_ringMap_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    proEtaleConstantRingMap (T := T) f ≫ proEtaleConstantRingMap (T := T) g =
      proEtaleConstantRingMap (T := T) (g.comp f) := by
  unfold proEtaleConstantRingMap
  rw [← Functor.map_comp]
  rfl

/-- The unique composition comparison fixed by balanced tensor on K-flat models. -/
theorem scalarExtensionFunctor_composition_existsUnique
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    ∃! α : scalarExtensionFunctor f T ⋙ scalarExtensionFunctor g T ≅
        scalarExtensionFunctor (g.comp f) T,
      ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
        CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing T A) P →
        α.hom.app (DerivedCategory.Q.obj P) ≫ scalarExtensionFunctorCounit (g.comp f) T P =
          (scalarExtensionFunctor g T).map (scalarExtensionFunctorCounit f T P) ≫
            scalarExtensionFunctorCounit g T
              ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) f)).obj P) ≫
            DerivedCategory.Q.map (reductionBalance T
              (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
              (proEtaleConstantRingMap (T := T) (g.comp f))
              (scalarExtensionFunctor_ringMap_comp f g T) P) := by
  obtain ⟨τ, hτ, huniq⟩ := derivedReductionComposition T
    (proEtaleConstantRingMap (T := T) f) (proEtaleConstantRingMap (T := T) g)
    (proEtaleConstantRingMap (T := T) (g.comp f))
    (scalarExtensionFunctor_ringMap_comp f g T)
  have := hτ.1
  refine ⟨asIso τ, ?_, ?_⟩
  · intro P hP
    exact hτ.2 P hP
  · intro α hα
    apply Iso.ext
    exact huniq α.hom ⟨inferInstance, hα⟩

/-- Canonical α, selected from its unique K-flat balancing characterization. -/
def scalarExtensionFunctor_composition
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    scalarExtensionFunctor f T ⋙ scalarExtensionFunctor g T ≅
      scalarExtensionFunctor (g.comp f) T :=
  (scalarExtensionFunctor_composition_existsUnique f g T).exists.choose

attribute [local irreducible] scalarExtensionFunctor_composition

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] scalarExtensionFunctorCounit
  completedAdicChangeData

end AlgebraicGeometry.ProEtale
