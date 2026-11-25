/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations

/-!
# Strict constant-coefficient tower operations

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-strict-constant-tower-operations).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

-- These elementary factorization calculations follow the proved helpers of
-- ProEtaleRingSheafChangeAdjunction, without importing its unrelated comparisons.
private theorem exactSquare_factorsh
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) (L' : C ⥤ D) (G : A ⥤ C) (H : B ⥤ D)
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : G ⋙ L' ≅ L ⋙ H) (K : HomotopyCategory A (.up ℤ)) :
    (Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso L H).symm).hom.app
          (DerivedCategory.Qh.obj K) ≫
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory s.hom (.up ℤ)).app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fach L H K
  have h₂ := Functor.mapDerivedCategoryCompIso_fach G L' K
  have h₃ := Functor.mapDerivedCategoryNatIso_fach s K
  apply (cancel_mono (DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h₁, h₃, ← h₂]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  have hc : DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [hc, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homotopy_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : HomotopyCategory B (.up ℤ)) :
    (mateEquiv (adj.mapHomotopyCategory (.up ℤ)) (adj'.mapHomotopyCategory (.up ℤ))
      (TwoSquare.mk _ _ _ _
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom ≫
          NatTrans.mapHomotopyCategory s.hom (.up ℤ) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv))).app K =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ =
    (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, Functor.mapHomologicalComplexCompIso]
  simp only [ NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  simp only [Functor.id_obj, NatIso.mapHomologicalComplex_hom_app_f, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, NatIso.mapHomologicalComplex_inv_app_f, Iso.refl_inv,
    Functor.map_comp, HomologicalComplex.id_f, Category.comp_id, Category.assoc,
    Functor.comp_map]
  change adj'.unit.app (G.obj (R.obj (K.X n))) ≫
      R'.map (𝟙 (L'.obj (G.obj (R.obj (K.X n))))) ≫
      R'.map (s.hom.app (R.obj (K.X n))) ≫
      R'.map (𝟙 (H.obj (L.obj (R.obj (K.X n))))) ≫
      R'.map (H.map (adj.counit.app (K.X n))) =
    𝟙 _ ≫ adj'.unit.app (G.obj (R.obj (K.X n))) ≫
      R'.map (s.hom.app (R.obj (K.X n))) ≫
      R'.map (H.map (adj.counit.app (K.X n))) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [R'.map_id, Category.id_comp, Category.id_comp]

private theorem derived_mate_factorsh
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : HomotopyCategory B (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategoryCompIso G L' ≪≫
            Functor.mapDerivedCategoryNatIso s ≪≫
            (Functor.mapDerivedCategoryCompIso L H).symm).hom)).app (DerivedCategory.Qh.obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactorsh.hom.app K) =
    G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory
            (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app K) ≫
      R'.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj K) := by
  rw [← homotopy_mate adj adj' s K]
  exact Adjunction.derived_mateEquiv_app_fac
    (adj.mapHomotopyCategory (.up ℤ)) (adj'.mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso A (.up ℤ)) (HomotopyCategory.quasiIso B (.up ℤ))
    (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso D (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit
    L'.mapDerivedCategoryFactorsh.hom R'.rightDerivedFunctorUnit
    G.mapDerivedCategoryFactorsh.hom H.mapDerivedCategoryFactorsh.hom
    (TwoSquare.mk _ _ _ _
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory s.hom (.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv))
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso L H).symm).hom)
    K (exactSquare_factorsh L L' G H s _)

private theorem adjunct_comp_comparison {C D E : Type*}
    [Category C] [Category D] [Category E]
    {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adj : L ⊣ R)
    (e : Rf ⋙ Rg ≅ R) {A : C} {B : D} {T : E}
    (h : A ⟶ Rg.obj B) (k : B ⟶ Rf.obj T) :
    (adj.homEquiv A T).symm (h ≫ Rg.map k ≫ e.hom.app T) =
      ((conjugateEquiv (adjg.comp adjf) adj).symm e.hom).app A ≫
        Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k := by
  apply (adj.homEquiv A T).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right]
  change _ = (adj.unit.app A ≫ R.map _) ≫ R.map _
  rw [← unit_conjugateEquiv_symm (adjg.comp adjf) adj e.hom A,
    Category.assoc, ← e.hom.naturality]
  conv_rhs => rw [← Category.assoc]
  change _ = ((adjg.comp adjf).homEquiv A T)
    (Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k) ≫ _
  rw [Adjunction.comp_homEquiv]
  change _ = (adjg.homEquiv _ _) ((adjf.homEquiv _ _) _) ≫ _
  rw [adjf.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjg.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp only [Category.assoc]

variable (B : Type (u + 1)) [CommRing B]

/-- Evaluation of the derived strict tower, keeping its actual derived-category source.
Source: blueprint, evaluation clauses (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev ev (X : Scheme.{u}) (n : ℕ) :
    Derived B X ⥤ DerivedCategory (Modules B X) :=
  ((evaluation ℕᵒᵖ (Modules B X)).obj (op n)).mapDerivedCategory

/-- Compatibility of the canonical constant-section identifications with composition.
Source: Stacks, Tag 0H7J (blueprint: def-cbc-strict-constant-tower-operations).
Proof: transpose both maps under inverse image. On every constant scalar both maps
are the same constant section; the sheafification universal property gives equality. -/
theorem constantRingIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    constantRingIso B (f ≫ g) = Scheme.proEtaleRingCompositeCoefficients f g
      (coefficients B Z) (coefficients B Y) (coefficients B X)
      (constantRingIso B g) (constantRingIso B f) := by
  apply Iso.ext
  let A := CommRingCat.of B
  change Scheme.proEtaleConstantInverseImageMap (f ≫ g) CommRingCat.{u + 1} A =
    (Scheme.proEtaleRingInverseImageComp f g).hom.app (coefficients B Z) ≫
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (Scheme.proEtaleConstantInverseImageMap g CommRingCat.{u + 1} A) ≫
      Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A
  let e := Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
        (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have hρ : Scheme.proEtaleConstantDirectImageMap (f ≫ g) CommRingCat.{u + 1} A =
      Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A ≫
        (Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) ≫
            e.hom.app ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
    apply ((sheafificationAdjunction (Scheme.ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj A) _).injective
    rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right]
    rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext U
    have hf := Equiv.apply_symm_apply
      ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
        ((Functor.const Y.ProEtᵒᵖ).obj A)
          ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)))
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
    have hfU := congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange g).op.obj U)) hf
    change (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        ((Scheme.proEtaleBaseChange g).op.obj U) ≫
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
        ((Scheme.proEtaleBaseChange g).op.obj U) =
          (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
            ((Scheme.proEtaleBaseChange f).op.obj ((Scheme.proEtaleBaseChange g).op.obj U)) at hfU
    change (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((Scheme.proEtaleBaseChange (f ≫ g)).op.obj U) =
      ((toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
          ((Scheme.proEtaleBaseChange g).op.obj U) ≫
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
          ((Scheme.proEtaleBaseChange g).op.obj U)) ≫
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
              ((MorphismProperty.Over.pullbackComp
                (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
    rw [hfU]
    have h := (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
    change 𝟙 A ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h
  change ((Scheme.proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1}).homEquiv _ _).symm _ = _
  rw [hρ]
  exact adjunct_comp_comparison (Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1})
    (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1})
    (Scheme.proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1}) e
    (Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A)
    (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A)

/-- Fibre-product pasting uniquely normalizes ordinary direct-image composition.
Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: evaluate both direct images on a test object. Restriction along the canonical
fibre-product pasting isomorphism gives the displayed map and its inverse. These are
linear by preservation of constant sections and natural by the universal property
of pullbacks. Equality on all sections proves uniqueness. -/
theorem moduleRComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! d : moduleDirectImage B f ⋙ moduleDirectImage B g ≅ moduleDirectImage B (f ≫ g),
      ∀ (N : Modules B X) (U : Z.ProEt)
        (m : ((moduleDirectImage B f ⋙ moduleDirectImage B g).obj N).val.obj (op U)),
        (d.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m := by
  obtain ⟨_, _, _, _, _, _, d, hd, _⟩ :=
    Scheme.proEtaleRingDerivedPullbackComposition f g
      (coefficients B Z) (coefficients B Y) (coefficients B X)
      (constantRingIso B g) (constantRingIso B f) (constantRingIso B (f ≫ g))
      (constantRingIso_comp B f g)
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (he N U.unop m).trans (hd N U.unop m).symm

/-- The section-normalized direct-image compositor. Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleRComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleDirectImage B f ⋙ moduleDirectImage B g ≅ moduleDirectImage B (f ≫ g) :=
  Classical.choose (moduleRComp_existsUnique B f g)

/-- Pullback composition is the unit-preserving conjugate of fibre-product pasting.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback B (f ≫ g) ≅ modulePullback B g ⋙ modulePullback B f :=
  (Adjunction.leftAdjointCompIso
    (Scheme.proEtaleRingModuleAdjunction g (coefficients B Z)
      (coefficients B Y) (constantRingIso B g))
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))
    (Scheme.proEtaleRingModuleAdjunction (f ≫ g) (coefficients B Z)
      (coefficients B X) (constantRingIso B (f ≫ g))) (moduleRComp B f g)).symm

/-- Strict tower pullback composition is the actual whiskered module comparison.
Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def towerGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    towerPullback B (f ≫ g) ≅ towerPullback B g ⋙ towerPullback B f :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleGComp B f g)) ≪≫
    Functor.whiskeringRightObjCompIso (modulePullback B g) (modulePullback B f)

/-- The pullback compositor descends from the actual termwise module compositor.
Source: Stacks, Tag 0D6D (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def gComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G B (f ≫ g) ≅ G B g ⋙ G B f :=
  Functor.mapDerivedCategoryNatIso (towerGComp B f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (towerPullback B g) (towerPullback B f)).symm

/-- The direct-image compositor is the conjugate for the composition adjunction.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def rComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R B f ⋙ R B g ≅ R B (f ≫ g) :=
  conjugateIsoEquiv ((adj B g).comp (adj B f)) (adj B (f ≫ g)) (gComp B f g)

/-- The identity direct image is the sectionwise pullback-identity comparison.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations).
Proof: the inverse base-change identity sends U to U ×_X X by its graph. Restrict
sections along this map. It preserves constant scalar sections, so is linear. Its
inverse is restriction along the inverse graph. Sections determine a unique map. -/
theorem moduleRId_existsUnique (X : Scheme.{u}) :
    ∃! e : moduleDirectImage B (𝟙 X) ≅ 𝟭 (Modules B X),
      ∀ (M : Modules B X) (U : X.ProEt)
        (m : ((moduleDirectImage B (𝟙 X)).obj M).val.obj (op U)),
        (e.hom.app M).val.app (op U) m =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op m := by
  let A := CommRingCat.of B
  let e := Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
      (Scheme.ProEt.topology X)
  have hρ : Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A =
      e.inv.app ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
    apply ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj A) _).injective
    rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_apply]
    apply NatTrans.ext
    funext U
    change (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((Scheme.proEtaleBaseChange (𝟙 X)).op.obj U) =
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app U ≫
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app U.unop).op
    have h := (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app U.unop).op
    change 𝟙 A ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h
  let i := MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X
  let S := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
  let φ : S ⟶ ((Scheme.proEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology X)).obj S :=
    ⟨Functor.whiskerRight (Scheme.proEtaleRingDirectImageMap (𝟙 X)
      (coefficients B X) (coefficients B X) (constantRingIso B (𝟙 X))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have hφ : Scheme.proEtaleRingDirectImageMap (𝟙 X)
      (coefficients B X) (coefficients B X) (constantRingIso B (𝟙 X)) =
        Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A := by
    exact Equiv.apply_symm_apply
      ((Scheme.proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).homEquiv _ _)
      (Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A)
  have he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans i.inv
      RingCat.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology X)).app S = 𝟙 S := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext a
    change (coefficients B X).obj.map (i.inv.app U.unop).op
      (((Scheme.proEtaleRingDirectImageMap (𝟙 X) (coefficients B X) (coefficients B X)
        (constantRingIso B (𝟙 X))).hom.app U) a) = a
    rw [hφ, hρ]
    change ((coefficients B X).obj.map (i.inv.app U.unop).op)
      ((coefficients B X).obj.map (i.hom.app U.unop).op a) = a
    change (((coefficients B X).obj.map (i.hom.app U.unop).op ≫
      (coefficients B X).obj.map (i.inv.app U.unop).op) a) = a
    rw [← Functor.map_comp, ← op_comp, i.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
    rfl
  let : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ X)).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) :=
    Functor.isContinuous_id (Scheme.ProEt.topology X)
  let d : moduleDirectImage B (𝟙 X) ≅ 𝟭 (Modules B X) :=
    SheafOfModules.pushforwardCongr₂ (φ := φ) i.symm he ≪≫ SheafOfModules.pushforwardId S
  have hd : ∀ (M : Modules B X) (U : X.ProEt)
      (m : ((moduleDirectImage B (𝟙 X)).obj M).val.obj (op U)),
      (d.hom.app M).val.app (op U) m = M.val.map (i.inv.app U).op m := by
    intro M U m
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (hd' M U.unop m).trans (hd M U.unop m).symm

/-- The section-normalized identity direct-image comparison.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleRId (X : Scheme.{u}) :
    moduleDirectImage B (𝟙 X) ≅ 𝟭 (Modules B X) :=
  Classical.choose (moduleRId_existsUnique B X)

/-- The inverse-image identity is the normalized conjugate of the sectionwise identity.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def gId (X : Scheme.{u}) : G B (𝟙 X) ≅ 𝟭 (Derived B X) :=
  Functor.mapDerivedCategoryNatIso
    (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      (Adjunction.leftAdjointIdIso
        (Scheme.proEtaleRingModuleAdjunction (𝟙 X) (coefficients B X)
          (coefficients B X) (constantRingIso B (𝟙 X))) (moduleRId B X))) ≪≫
      Functor.whiskeringRightObjIdIso) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The normalized derived direct-image identity.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def rId (X : Scheme.{u}) : R B (𝟙 X) ≅ 𝟭 (Derived B X) :=
  (conjugateIsoEquiv Adjunction.id (adj B (𝟙 X)) (gId B X)).symm

/-- Evaluation commutes with strict termwise inverse image.
Source: blueprint evaluation normalization
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: both object maps evaluate the same strict tower at n and apply the same
module functor. Their maps are the same evaluated natural transformations. -/
theorem evaluationPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    towerPullback B f ⋙ (evaluation ℕᵒᵖ (Modules B X)).obj (op n) =
      (evaluation ℕᵒᵖ (Modules B Y)).obj (op n) ⋙ modulePullback B f := by
  rfl

/-- The evaluation/pullback comparison induced by the actual termwise equality.
Source: blueprint evaluation normalization
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def evalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    G B f ⋙ ev B X n ≅ ev B Y n ⋙ (modulePullback B f).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
  Functor.mapDerivedCategoryNatIso (eqToIso (evaluationPullback B f n)) ≪≫
  (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The direct-image evaluation map is its specified adjunction mate.
Source: Stacks, Tags 07A7 and 0DVC
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def evalR {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    R B f ⋙ ev B Y n ⟶ ev B X n ⋙ (moduleDirectImage B f).rightDerivedFunctor :=
  mateEquiv (adj B f)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).mapDerivedCategoryRightDerivedAdjunction
    (evalG B f n).inv

private theorem evaluation_mate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv
      ((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
        (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ)
      (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
        (coefficients B X) (constantRingIso B f))
      (TwoSquare.mk _ _ _ _ (eqToIso (evaluationPullback B f n)).inv)) =
        𝟙 ((evaluation ℕᵒᵖ (Modules B X)).obj (op n) ⋙ moduleDirectImage B f) := by
  apply NatTrans.ext
  funext T
  change (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).unit.app
        ((moduleDirectImage B f).obj (T.obj (op n))) ≫
      (moduleDirectImage B f).map
        ((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
          (coefficients B X) (constantRingIso B f)).counit.app (T.obj (op n))) = 𝟙 _
  exact (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).right_triangle_components _

/-- This normalized mate is invertible, without a uniform lower bound.
Source: blueprint evaluation proof step, and Stacks, Tag 08BJ
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: a K-injective strict tower evaluates to a K-injective complex: evaluation
has an exact left adjoint given by sums over the index arrows. On such a
representative both direct images give the identical evaluated complex.
The homotopy adjunction is termwise, so the derived Hom bijection identifies
this equality with the displayed mate, including its unit and counit. -/
theorem evalR_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (evalR B f n) := by
  let L := towerPullback B f
  let L' := modulePullback B f
  let P := towerDirectImage B f
  let P' := moduleDirectImage B f
  let E := (evaluation ℕᵒᵖ (Modules B Y)).obj (op n)
  let E' := (evaluation ℕᵒᵖ (Modules B X)).obj (op n)
  have : PreservesFiniteLimits L := towerPullback_finiteLimits B f
  have : PreservesFiniteColimits L := towerPullback_finiteColimits B f
  have : PreservesFiniteLimits L' := modulePullback_finiteLimits B f
  have : PreservesFiniteColimits L' := modulePullback_finiteColimits B f
  let a : L ⊣ P := (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ
  let a' : L' ⊣ P' := Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)
  let s : E ⋙ L' ≅ L ⋙ E' := (eqToIso (evaluationPullback B f n)).symm
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  have hfac := derived_mate_factorsh a a' s H
  let hEval : CochainComplex.IsKInjective
      ((E'.mapHomologicalComplex (.up ℤ)).obj I) :=
    tower_evaluation_isKInjective (Modules B X) I (op n)
  have hP : IsIso (P.rightDerivedFunctorUnit.app H) := inferInstance
  have hP' : IsIso (P'.rightDerivedFunctorUnit.app
      ((E'.mapHomotopyCategory (.up ℤ)).obj H)) := by
    change IsIso (P'.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((E'.mapHomologicalComplex (.up ℤ)).obj I)))
    infer_instance
  have hm : (mateEquiv a a' (TwoSquare.mk _ _ _ _ s.hom)) =
      𝟙 (E' ⋙ P') := evaluation_mate B f n
  have hs : (Functor.mapDerivedCategoryCompIso E L' ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫
      (Functor.mapDerivedCategoryCompIso L E').symm).hom = (evalG B f n).inv := by
    dsimp only [s, evalG]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rfl
  have hh : IsIso
      ((NatTrans.mapHomotopyCategory
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app H) := by
    rw [hm]
    change IsIso ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (𝟙 (E' ⋙ P')) (.up ℤ)).app I))
    have hId : (NatTrans.mapHomologicalComplex (𝟙 (E' ⋙ P')) (.up ℤ)).app I =
        𝟙 _ := by ext k; rfl
    rw [hId, CategoryTheory.Functor.map_id]
    infer_instance
  have hcomp : IsIso (E.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app H) ≫
      (evalR B f n).app (DerivedCategory.Qh.obj H) ≫
        P'.rightDerivedFunctor.map (E'.mapDerivedCategoryFactorsh.hom.app H)) := by
    change IsIso (E.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app H) ≫
      (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
        a'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (evalG B f n).inv)).app
          (DerivedCategory.Qh.obj H) ≫
        P'.rightDerivedFunctor.map (E'.mapDerivedCategoryFactorsh.hom.app H))
    rw [← hs, hfac]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance
    (@IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hcomp)

end AlgebraicGeometry.ProEtale.StrictTower
