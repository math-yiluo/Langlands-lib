/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.FlatCoverFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel

/-! # Bounded flat models for the coefficient-model Tor test

Source: Stacks Project, Tags 08G0 and 08G1.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})

private local instance moduleMonoidal : MonoidalCategory (ConstantCompletion.Mod R) :=
  SheafOfModules.monoidalCategory R
private local instance moduleSymmetric : SymmetricCategory (ConstantCompletion.Mod R) :=
  SheafOfModules.symmetricCategory R
private local instance moduleClosed : MonoidalClosed (ConstantCompletion.Mod R) :=
  Classical.choice (SheafOfModules.tensorClosed R).2.1
private local instance modulePreadditive : MonoidalPreadditive (ConstantCompletion.Mod R) :=
  Classical.choice (SheafOfModules.tensorClosed R).1
private local instance moduleGrothendieck : IsGrothendieckAbelian.{w} (ConstantCompletion.Mod R) :=
  SheafOfModules.isGrothendieckAbelian _

private theorem categorical_flat_iff (M : ConstantCompletion.Mod R) :
    ObjectProperty.flat M ↔ SheafOfModules.IsFlat (R := R) M := by
  constructor
  · exact fun h ↦ h.2
  · intro h
    have : PreservesFiniteLimits (tensorRight M) := h.1
    exact (ObjectProperty.flat_iff_preservesFiniteLimits M).2
      (preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight M).symm (F := tensorRight M))

private theorem moduleFlatResolution :
    Abelian.HasFunctorialFlatResolution (ConstantCompletion.Mod R) := by
  obtain ⟨T, π, hT⟩ := SheafOfModules.exists_functorial_flat_cover J R
  exact ⟨{
    F := ObjectProperty.flat.lift T (fun M ↦ (categorical_flat_iff R _).mpr (hT M).1)
    π := π
    epi_π_app := fun M ↦ (hT M).2 }⟩

private local instance standardDerived : HasDerivedCategory (ConstantCompletion.Mod R) :=
  HasDerivedCategory.standard _

private local instance flatResolution :
    Abelian.HasFunctorialFlatResolution (ConstantCompletion.Mod R) :=
  moduleFlatResolution R

private local instance smallColimits : HasColimitsOfSize.{0, 0} (ConstantCompletion.Mod R) :=
  hasColimitsOfSizeShrink.{0, 0, w, w} _

private theorem nativeKFlat_iff (P : ConstantCompletion.Cx R) :
    (HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ)).kFlat P ↔
      P.IsKFlatIndependentCoefficients := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  constructor
  · intro h Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
      (h ((HomotopyCategory.quotient _ (.up ℤ)).obj Z)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mpr hZ)).2
  · intro h Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    have hZ' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mp hZ
    have ht := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z P (curriedTensor _))).mpr (h Z hZ')
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) ht, ht⟩

private theorem nativeTor_iff (K : ConstantCompletion.D R) (a b : ℤ) (hab : a ≤ b) :
    DerivedCategory.torAmplitudeIn (ConstantCompletion.Mod R) a b K ↔
      HasCoefficientModelTorAmplitude R K a b := by
  let A := ConstantCompletion.Mod R
  have modelIso {L : ConstantCompletion.D R} (P : ConstantCompletion.Cx R)
      (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
      (e : (ConstantCompletion.Q R).obj P ≅ L) (M : A) :
      L ⊗ (DerivedCategory.singleFunctor A 0).obj M ≅
        (ConstantCompletion.Q R).obj
          (((ringedKoszulTensor R).obj P).obj ((HomologicalComplex.single A (.up ℤ) 0).obj M)) :=
    tensorIso e.symm ((DerivedCategory.singleFunctorIsoCompQ A 0).app M) ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P _ hP
  constructor
  · intro hK
    refine ⟨hab, ?_⟩
    intro P hP ⟨e⟩ M q hq
    have hp := (nativeKFlat_iff R P).mpr hP
    have ht := hK M
    have hs := (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (modelIso P hp e M) ht
    have hz : IsZero ((DerivedCategory.homologyFunctor A q).obj
        ((ConstantCompletion.Q R).obj
          (((ringedKoszulTensor R).obj P).obj
            ((HomologicalComplex.single A (.up ℤ) 0).obj M)))) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ a).mp hs.1 q hq
      · exact (DerivedCategory.isLE_iff _ b).mp hs.2 q hq
    exact hz.of_iso ((DerivedCategory.homologyFunctorFactors A q).symm.app _)
  · intro hK M
    let G := (ConstantCompletion.Q R).objPreimage K
    obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat G
    have : QuasiIso π := hπ
    have : IsIso ((ConstantCompletion.Q R).map π) := by infer_instance
    let e : (ConstantCompletion.Q R).obj P ≅ K :=
      asIso ((ConstantCompletion.Q R).map π) ≪≫ (ConstantCompletion.Q R).objObjPreimageIso K
    have hz (q : ℤ) (hq : q < a ∨ b < q) :
        IsZero ((DerivedCategory.homologyFunctor A q).obj
          (K ⊗ (DerivedCategory.singleFunctor A 0).obj M)) := by
      have ht := hK.2 P ((nativeKFlat_iff R P).mp hP) ⟨e⟩ M q hq
      exact ht.of_iso ((DerivedCategory.homologyFunctor A q).mapIso
        (modelIso P hP e M) ≪≫ (DerivedCategory.homologyFunctorFactors A q).app _)
    exact ⟨(DerivedCategory.isGE_iff _ a).mpr (fun q hq ↦ hz q (Or.inl hq)),
      (DerivedCategory.isLE_iff _ b).mpr (fun q hq ↦ hz q (Or.inr hq))⟩

end CategoryTheory
