/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.MorphismProperty.Comma
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-!
# Compatible changes of ring sheaves and derived adjunctions

## References

* Stacks Project, Cohomology on Sites, Tags 0D6D, 0D6E and 07A6
* Stacks, Tag 07A5
* Stacks, Tags 05RT, 0D6D, 0D6E and 07A6
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

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
        Functor.mapDerivedCategoryNatIso s ≪≫
        (Functor.mapDerivedCategoryCompIso L H).symm).hom.app
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

private noncomputable def chainDerivedUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K)

private theorem quotient_hom_id {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).hom.app K = 𝟙 (DerivedCategory.Q.obj K) := rfl

private theorem quotient_inv_id {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).inv.app K = 𝟙 (DerivedCategory.Q.obj K) := rfl

private theorem homotopyFactors_inv_id
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K =
      𝟙 ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) := rfl

private theorem chainDerivedUnit_isIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) [K.IsKInjective] :
    IsIso (chainDerivedUnit F K) := by
  dsimp only [chainDerivedUnit]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem chainDerivedUnit_isIso_of_resolution
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K J : CochainComplex A ℤ) [J.IsKInjective]
    (j : K ⟶ J) [QuasiIso j]
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map j)] :
    IsIso (chainDerivedUnit F K) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have hj : IsIso (DerivedCategory.Qh.map (q.map j)) := by
    change IsIso (DerivedCategory.Q.map j)
    infer_instance
  have hFj : IsIso (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (q.map j))) := by
    change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j))
    infer_instance
  have hn := F.rightDerivedFunctorUnit.naturality (q.map j)
  dsimp only [Functor.comp_map] at hn
  have hJ : IsIso (F.rightDerivedFunctorUnit.app (q.obj J)) := inferInstance
  have hcomp : IsIso (F.rightDerivedFunctorUnit.app (q.obj K) ≫
      F.rightDerivedFunctor.map (DerivedCategory.Qh.map (q.map j))) := by
    rw [← hn]
    infer_instance
  have : IsIso (F.rightDerivedFunctorUnit.app (q.obj K)) :=
    IsIso.of_isIso_comp_right _ (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (q.map j)))
  dsimp only [chainDerivedUnit]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_mate_factors
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
    (K : CochainComplex B ℤ) :
    G.mapDerivedCategory.map (chainDerivedUnit R K) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategoryCompIso G L' ≪≫
            Functor.mapDerivedCategoryNatIso s ≪≫
            (Functor.mapDerivedCategoryCompIso L H).symm).hom)).app (DerivedCategory.Q.obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
    G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app K) ≫
      chainDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj K) := by
  have hf := derived_mate_factorsh adj adj' s ((HomotopyCategory.quotient _ _).obj K)
  have hG := G.mapDerivedCategoryFactorsh_hom_app
    ((R.mapHomologicalComplex (.up ℤ)).obj K)
  change G.mapDerivedCategoryFactorsh.hom.app
      ((R.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) = _ at hG
  rw [hG] at hf
  have hq : (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := rfl
  have hq' : (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := rfl
  have hτ : DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app
          ((HomotopyCategory.quotient _ _).obj K)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app K) := rfl
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app, hq, hq', hτ,
    chainDerivedUnit, quotient_hom_id, quotient_inv_id, homotopyFactors_inv_id,
    CategoryTheory.Functor.map_comp, Category.assoc] at hf ⊢
  repeat first
    | erw [G.mapDerivedCategory.map_id] at hf
    | erw [H.mapDerivedCategory.map_id] at hf
    | erw [R'.rightDerivedFunctor.map_id] at hf
    | erw [(DerivedCategory.Qh (C := C)).map_id] at hf
    | erw [(DerivedCategory.Qh (C := D)).map_id] at hf
    | erw [Category.id_comp] at hf
    | erw [Category.comp_id] at hf
  repeat first
    | erw [G.mapDerivedCategory.map_id]
    | erw [R.rightDerivedFunctor.map_id]
    | erw [R'.rightDerivedFunctor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  exact hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_comp_ext
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions A]
    (R : A ⥤ B) (G : B ⥤ C) [R.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (T : DerivedCategory A ⥤ DerivedCategory C)
    (x y : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶ T)
    (h : ∀ K : CochainComplex A ℤ,
      G.mapDerivedCategory.map (chainDerivedUnit R K) ≫ x.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (chainDerivedUnit R K) ≫ y.app (DerivedCategory.Q.obj K)) :
    x = y := by
  apply Functor.rightDerived_ext (R.rightDerivedFunctor ⋙ G.mapDerivedCategory)
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit R G)
    (HomotopyCategory.quasiIso A (.up ℤ)) T x y
  apply NatTrans.ext
  funext K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hx := x.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
  have hy := y.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
  dsimp only [Functor.comp_map] at hx hy
  have hk := h K
  dsimp only [chainDerivedUnit] at hk
  simp only [Functor.map_comp, Category.assoc] at hk
  erw [hx, hy] at hk
  have hk' := (cancel_epi (G.mapDerivedCategory.map
    ((DerivedCategory.quotientCompQhIso B).inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj K)))).mp hk
  have hk'' := (cancel_mono
    (T.map ((DerivedCategory.quotientCompQhIso A).hom.app K))).mp
      (by simpa only [← Category.assoc] using hk')
  dsimp [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  erw [hk'']
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_adjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : TwoSquare G L L' H)
    (M : A) (N : B) (t : L.obj M ⟶ N) :
    adj'.homEquiv _ _ (s.app M ≫ H.map t) =
      G.map (adj.homEquiv M N t) ≫ (mateEquiv adj adj' s).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_mateEquiv adj adj' s M
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := (mateEquiv adj adj' s).naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]

private theorem isoOfAdjunct
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) {X : A} {Y Z : B} (g : X ⟶ R.obj Y) (h : X ⟶ R.obj Z)
    (k : Y ⟶ Z) (hg : IsIso ((adj.homEquiv X Y).symm g))
    (hh : IsIso ((adj.homEquiv X Z).symm h)) (hk : g ≫ R.map k = h) : IsIso k := by
  let := hg
  let := hh
  have : IsIso ((adj.homEquiv X Y).symm g ≫ k) := by
    rw [← adj.homEquiv_naturality_right_symm, hk]
    exact hh
  exact IsIso.of_isIso_comp_left ((adj.homEquiv X Y).symm g) k

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringUnitComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (adj : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c)
    (M : proEtaleRingModules Y R) :
    IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj M)
      ((SheafOfModules.toSheaf _).obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        ((SheafOfModules.toSheaf _).map (adj.unit.app M))) := by
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let C := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let P := SheafOfModules.toSheaf.{u + 1} A
  let Q := SheafOfModules.toSheaf.{u + 1} B
  let Q' := SheafOfModules.toSheaf.{u + 1} C
  let a := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  obtain ⟨a₀, h₀⟩ := proEtaleModuleInverseImage_canonicalUnitComparison f R
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let a₁ : proEtaleRingExtension f R S c ⊣
      SheafOfModules.restrictScalars.{u + 1} rc.hom :=
    proEtaleRingExtensionAdjunction f R S c
  have : (SheafOfModules.restrictScalars.{u + 1} rc.hom).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence X rc).functor.IsEquivalence
  have : IsIso a₁.unit := by infer_instance
  have : IsIso (a₁.unit.app ((proEtaleModuleInverseImage f R).obj M)) := inferInstance
  let ac := a₀.comp a₁
  change proEtaleRingModulePullback f R S c ⊣ _ at ac
  let T := SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (S := A) (R := B)
      ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let er : SheafOfModules.restrictScalars rc.hom ⋙ T ≅
      proEtaleRingModuleDirectImage f R S c := by
    refine NatIso.ofComponents (fun N ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
    · intro N N' h
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      rfl
  let ab := ac.ofNatIsoRight er
  let β₀ := (a.homEquiv (P.obj M)
    (Q.obj ((proEtaleModuleInverseImage f R).obj M))).symm
      (P.map (a₀.unit.app M))
  have : IsIso β₀ := h₀ M
  let k := Q.map (a₁.unit.app ((proEtaleModuleInverseImage f R).obj M))
  have : IsIso k := inferInstance
  have he : (a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (ab.unit.app M)) = β₀ ≫ k := by
    rw [← a.homEquiv_naturality_right_symm]
    congr 1
  have hb : IsIso ((a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (ab.unit.app M))) := by
    rw [he]
    infer_instance
  let e := ab.leftAdjointUniq adj
  have hu := Adjunction.unit_leftAdjointUniq_hom_app ab adj M
  have hh : (a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (adj.unit.app M)) =
      (a.homEquiv (P.obj M)
        (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
          (P.map (ab.unit.app M)) ≫ Q'.map (e.hom.app M) := by
    rw [← a.homEquiv_naturality_right_symm]
    congr 1
    rw [← hu, P.map_comp]
    rfl
  change IsIso ((a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (adj.unit.app M)))
  rw [hh]
  infer_instance

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteLimits

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteColimits

variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)

include comm in
private theorem restrictionDirectImageMap_square :
    aV ≫ proEtaleRingDirectImageMap f SV SU cS =
      proEtaleRingDirectImageMap f RV RU cR ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map aU := by
  dsimp [proEtaleRingDirectImageMap]
  have hn := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.naturality aV
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Functor.map_comp, ← comm, Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include comm in
private noncomputable def restrictionDirectImageHom (N : proEtaleRingModules U SU) :
    ((proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV).obj N) ⟶
      ((proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR).obj N) where
  val :=
    { app W := ModuleCat.ofHom
        (X := ((proEtaleRingModuleDirectImage f SV SU cS ⋙
          proEtaleRingRestrictScalars aV).obj N).val.obj W)
        (Y := ((proEtaleRingRestrictScalars aU ⋙
          proEtaleRingModuleDirectImage f RV RU cR).obj N).val.obj W)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r n
            change (proEtaleRingDirectImageMap f SV SU cS).hom.app W
                (aV.hom.app W r) • (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n) =
              aU.hom.app ((proEtaleBaseChange f).op.obj W)
                ((proEtaleRingDirectImageMap f RV RU cR).hom.app W r) •
                (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n)
            congr 1
            exact congrArg (fun h ↦ h.hom.app W r)
              (restrictionDirectImageMap_square f RV SV RU SU aV aU cR cS comm) }
      naturality := by intros; ext n; rfl }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include comm in
private noncomputable def restrictionDirectImageInv (N : proEtaleRingModules U SU) :
    ((proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR).obj N) ⟶
      ((proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV).obj N) where
  val :=
    { app W := ModuleCat.ofHom
        (X := ((proEtaleRingRestrictScalars aU ⋙
          proEtaleRingModuleDirectImage f RV RU cR).obj N).val.obj W)
        (Y := ((proEtaleRingModuleDirectImage f SV SU cS ⋙
          proEtaleRingRestrictScalars aV).obj N).val.obj W)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r n
            change aU.hom.app ((proEtaleBaseChange f).op.obj W)
                ((proEtaleRingDirectImageMap f RV RU cR).hom.app W r) •
                (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n) =
              (proEtaleRingDirectImageMap f SV SU cS).hom.app W
                (aV.hom.app W r) • (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n)
            congr 1
            exact congrArg (fun h ↦ h.hom.app W r)
              (restrictionDirectImageMap_square f RV SV RU SU aV aU cR cS comm).symm }
      naturality := by intros; ext n; rfl }

include comm in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringModuleMap_isIso
    (M : proEtaleRingModules V SV) (N : proEtaleRingModules U RU)
    (N' : proEtaleRingModules U SU)
    (g : (proEtaleRingRestrictScalars aV).obj M ⟶
      (proEtaleRingModuleDirectImage f RV RU cR).obj N)
    (h : M ⟶ (proEtaleRingModuleDirectImage f SV SU cS).obj N')
    (k : N ⟶ (proEtaleRingRestrictScalars aU).obj N')
    (hg : IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj ((proEtaleRingRestrictScalars aV).obj M))
      ((SheafOfModules.toSheaf _).obj N)).symm ((SheafOfModules.toSheaf _).map g)))
    (hh : IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj M)
      ((SheafOfModules.toSheaf _).obj N')).symm ((SheafOfModules.toSheaf _).map h)))
    (hk : g ≫ (proEtaleRingModuleDirectImage f RV RU cR).map k =
      (proEtaleRingRestrictScalars aV).map h ≫
        (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app N') :
    IsIso k := by
  let P := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology V)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
  let P' := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology V)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SV)
  let Q := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)
  let Q' := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SU)
  let a := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  have he : P.map
      ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app N') =
      𝟙 _ := by
    ext W n
    exact (Classical.choose_spec
      (proEtaleRingRestrictionDirectImage_existsUnique
        f RV SV RU SU aV aU cR cS comm)).1 _ W n
  have htP := congrArg P.map hk
  simp only [P.map_comp, he] at htP
  erw [Category.comp_id] at htP
  have htP' : P.map g ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
      (Q.map k) = P'.map h := by
    ext W n
    exact ConcreteCategory.congr_hom (congrArg (fun z ↦ z.hom.app W) htP) n
  have : IsIso (Q.map k) := isoOfAdjunct a (X := P'.obj M) (Y := Q.obj N) (Z := Q'.obj N')
    (P.map g) (P'.map h) (Q.map k) hg hh htP'
  exact isIso_of_reflects_iso k Q

attribute [local irreducible] proEtaleRingRestrictionPullbackApp
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionPullback_mate :
    (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
      (proEtaleRingModuleAdjunction f RV RU cR)
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm))) =
      (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom := by
  change (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
    (proEtaleRingModuleAdjunction f RV RU cR))
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)) =
      TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom
  rw [← Equiv.eq_symm_apply]
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [mateEquiv_symm_apply, proEtaleRingRestrictionPullbackInv,
    proEtaleRingRestrictionPullbackApp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_map,
    Category.id_comp]
  simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  exact congrArg (fun h ↦ _ ≫ _ ≫ h) (Category.comp_id _).symm

/-- The termwise descended identified-coefficient inverse-image comparison `b`. -/
noncomputable def proEtaleRingRestrictionDerivedPullback :
    proEtaleRingDerivedPullback f SV SU cS ⋙ (proEtaleRingRestrictScalars aU).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aV).mapDerivedCategory ⋙
        proEtaleRingDerivedPullback f RV RU cR :=
  (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback f SV SU cS)
    (proEtaleRingRestrictScalars aU)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)).symm ≪≫
    (Functor.mapDerivedCategoryCompIso (proEtaleRingRestrictScalars aV)
      (proEtaleRingModulePullback f RV RU cR)).symm

/-- The right-derived unit on complexes, including the canonical quotient identifications. -/
noncomputable def proEtaleRingDirectImageDerivedUnit
    (K : CochainComplex (proEtaleRingModules U RU) ℤ) :
    DerivedCategory.Q.obj
        (((proEtaleRingModuleDirectImage f RV RU cR).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (proEtaleRingDerivedDirectImage f RV RU cR).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (proEtaleRingModuleDirectImage f RV RU cR).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K) ≫
    (proEtaleRingDerivedDirectImage f RV RU cR).map
      ((DerivedCategory.quotientCompQhIso _).hom.app K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringed_resolution
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology C) (K : GrothendieckTopology D)
    (S : GrothendieckTopology E)
    (R : Sheaf T CommRingCat.{u}) (Z : Sheaf K CommRingCat.{u})
    (W : Sheaf S CommRingCat.{u})
    (r : RingedToposMorphism
      ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj Z))
    (p : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj Z)
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj W)) :
    letI := r.additive
    letI := p.additive
    ∀ (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ),
      I.IsKInjective →
    ∀ (J : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj Z)) ℤ),
      J.IsKInjective →
    ∀ j : (r.modules.mapHomologicalComplex (.up ℤ)).obj I ⟶ J,
      QuasiIso j → QuasiIso ((p.modules.mapHomologicalComplex (.up ℤ)).map j) := by
  have := r.additive
  have := p.additive
  intro I hI J hJ j hj
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj Z))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj W))
  obtain ⟨Rf, Rg, Rgf, ηf, ηg, ηgf, hf, hg, hgf, hIf, hIg, κ, hκ, _⟩ :=
    ringedToposDerivedPushforwardComposition T K S R Z W r p
  exact (hκ.2 I hI J hJ j).1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quasiIso_map_of_models
    {M A B M' A' B' : Type*}
    [Category M] [Category A] [Category B] [Category M'] [Category A'] [Category B']
    [Abelian M] [Abelian A] [Abelian B] [Abelian M'] [Abelian A'] [Abelian B']
    (FM : M ⥤ M') (FA : A ⥤ A') (FB : B ⥤ B')
    [FM.Additive] [FA.Additive] [FB.Additive]
    [FA.PreservesHomology] [FB.PreservesHomology] [FB.ReflectsIsomorphisms]
    [FM.PreservesKInjectiveComplexes] [FA.PreservesKInjectiveComplexes]
    (r : M' ⥤ A') (p : A' ⥤ B') [r.Additive] [p.Additive]
    (H : M ⥤ A) (G : A ⥤ B) [H.Additive] [G.Additive]
    (α : FM ⋙ r ≅ H ⋙ FA) (β : FA ⋙ p ≅ G ⋙ FB)
    (h : ∀ (I : CochainComplex M' ℤ), I.IsKInjective →
      ∀ (J : CochainComplex A' ℤ), J.IsKInjective →
      ∀ j : (r.mapHomologicalComplex (.up ℤ)).obj I ⟶ J,
      QuasiIso j → QuasiIso ((p.mapHomologicalComplex (.up ℤ)).map j))
    (I : CochainComplex M ℤ) [I.IsKInjective]
    (J : CochainComplex A ℤ) [J.IsKInjective]
    (j : (H.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) := by
  let αc := Functor.mapHomologicalComplexCompIso (F := FM) (G := r) α (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ FA)) (.up ℤ)).symm
  let βc := Functor.mapHomologicalComplexCompIso (F := FA) (G := p) β (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ FB)) (.up ℤ)).symm
  let Mc := FM.mapHomologicalComplex (.up ℤ)
  let Ac := FA.mapHomologicalComplex (.up ℤ)
  let Bc := FB.mapHomologicalComplex (.up ℤ)
  let pc := p.mapHomologicalComplex (.up ℤ)
  let vc := G.mapHomologicalComplex (.up ℤ)
  have : QuasiIso (Ac.map j) := HomologicalComplex.quasiIso_map_of_preservesHomology j FA
  let j' := αc.hom.app I ≫ Ac.map j
  have : QuasiIso j' := by
    dsimp only [j']
    infer_instance
  have hMI : CochainComplex.IsKInjective (Mc.obj I) := inferInstance
  have hAJ : CochainComplex.IsKInjective (Ac.obj J) := inferInstance
  have hq : QuasiIso (pc.map j') := h (Mc.obj I) hMI (Ac.obj J) hAJ j' inferInstance
  have : QuasiIso (pc.map (αc.hom.app I) ≫ pc.map (Ac.map j)) := by
    simpa only [j', Functor.map_comp] using hq
  have : QuasiIso (pc.map (Ac.map j)) :=
    quasiIso_of_comp_left (pc.map (αc.hom.app I)) _
  have hn := βc.hom.naturality j
  dsimp only [Functor.comp_map] at hn
  have hq' : QuasiIso (pc.map (Ac.map j) ≫ βc.hom.app J) := inferInstance
  rw [hn] at hq'
  have : QuasiIso (Bc.map (vc.map j)) :=
    quasiIso_of_comp_left (βc.hom.app _) _
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (vc.map j) FB).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem restriction_directImage_quasiIso
    (I : CochainComplex (proEtaleRingModules U SU) ℤ) [I.IsKInjective]
    (J : CochainComplex (proEtaleRingModules U RU) ℤ) [J.IsKInjective]
    (j : ((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    QuasiIso (((proEtaleRingModuleDirectImage f RV RU cR).mapHomologicalComplex (.up ℤ)).map
      j) := by
  -- Present restriction and direct image on small sites; both transports retain sections.
  let eu := AsSmall.equiv.{u, u + 1, u + 1} (C := U.ProEt)
  let ev := AsSmall.equiv.{u, u + 1, u + 1} (C := V.ProEt)
  let T := proEtaleModelTopology U
  let S := proEtaleModelTopology V
  let F := proEtaleModelBaseChange f
  have : F.IsContinuous S T := proEtaleModelBaseChange_isContinuous f
  have : (AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt).IsEquivalence :=
    inferInstanceAs ev.inverse.IsEquivalence
  have : (AsSmall.up : U.ProEt ⥤ proEtaleSiteModel U).IsEquivalence :=
    inferInstanceAs eu.functor.IsEquivalence
  have : PreservesFiniteLimits F := by
    dsimp only [F, proEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits _
  let L := Functor.sheafPullbackConstruction.sheafPullback F (Type (u + 1)) S T
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    F (Type (u + 1)) S T
  have : (AsSmall.down : proEtaleSiteModel U ⥤ U.ProEt).IsContinuous
      T (ProEt.topology U) :=
    by
      dsimp only [T]
      infer_instance
  have : (AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt).IsContinuous
      S (ProEt.topology V) :=
    by
      dsimp only [S]
      infer_instance
  let TU := (AsSmall.down : proEtaleSiteModel U ⥤ U.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} T (ProEt.topology U)
  let TV := (AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} S (ProEt.topology V)
  let R := TU.obj SU
  let Z := TU.obj RU
  let W := TV.obj RV
  let φ : W ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} S T).obj Z :=
    TV.map (proEtaleRingDirectImageMap f RV RU cR)
  obtain ⟨p, hp⟩ := continuousRingedToposModuleDirectImage_exists F L adj Z W φ
  let a := (sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (TU.map aU)
  obtain ⟨r, hr⟩ := restrictionRingedToposModuleDirectImage_exists a
  let P := p.modules
  let A := r.modules
  let eM := (proEtaleModuleModelEquivalence U
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SU)).symm
  let eA := (proEtaleModuleModelEquivalence U
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)).symm
  let eB := (proEtaleModuleModelEquivalence V
    ((sheafCompose (ProEt.topology V) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).symm
  let EM := proEtaleModuleToModel
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SU)
  let EA := proEtaleModuleToModel
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)
  let EB := proEtaleModuleToModel
    ((sheafCompose (ProEt.topology V) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
  have : EM.IsEquivalence := inferInstanceAs eM.functor.IsEquivalence
  have : EA.IsEquivalence := inferInstanceAs eA.functor.IsEquivalence
  have : EB.IsEquivalence := inferInstanceAs eB.functor.IsEquivalence
  have : EM.Additive := EM.additive_of_preserves_binary_products
  have : EA.Additive := EA.additive_of_preserves_binary_products
  have : EB.Additive := EB.additive_of_preserves_binary_products
  have : PreservesFiniteLimits EA := inferInstance
  have : PreservesFiniteColimits EA := inferInstance
  have : EA.PreservesHomology := inferInstance
  have : PreservesFiniteLimits EB := inferInstance
  have : PreservesFiniteColimits EB := inferInstance
  have : EB.PreservesHomology := inferInstance
  have : EB.ReflectsIsomorphisms := inferInstance
  have : EM.PreservesKInjectiveComplexes := inferInstance
  have : EA.PreservesKInjectiveComplexes := inferInstance
  have : P.Additive := p.additive
  have : A.Additive := r.additive
  let H := proEtaleRingRestrictScalars aU
  let G := proEtaleRingModuleDirectImage f RV RU cR
  have : H.Additive := inferInstanceAs (proEtaleRingRestrictScalars aU).Additive
  have : G.Additive := inferInstanceAs (proEtaleRingModuleDirectImage f RV RU cR).Additive
  let α : EM ⋙ A ≅ H ⋙ EA := by
    dsimp only [A]
    rw [hr]
    exact NatIso.ofComponents
      (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
          intro W W' a
          ext x
          rfl))) (by
        intro M N h
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        rfl)
  let β : EA ⋙ P ≅ G ⋙ EB := by
    dsimp only [P]
    rw [hp]
    exact NatIso.ofComponents
      (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
          intro W W' a
          ext x
          rfl))) (by
        intro M N h
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        rfl)
  exact quasiIso_map_of_models EM EA EB A P H G α β
    (ringed_resolution T T S R Z W r p) I J j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def canonicalDerivedMate :
    proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ⟶
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR :=
  (mateEquiv (proEtaleRingDerivedAdjunction f SV SU cS)
    (proEtaleRingDerivedAdjunction f RV RU cR)
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm).inv))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonicalDerivedMate_factors
    (K : CochainComplex (proEtaleRingModules U SU) ℤ) :
      (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
          (chainDerivedUnit (proEtaleRingModuleDirectImage f SV SU cS) K) ≫
        (canonicalDerivedMate f RV SV RU SU aV aU cR cS comm).app (DerivedCategory.Q.obj K) ≫
        (proEtaleRingDerivedDirectImage f RV RU cR).map
          ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K) =
      (proEtaleRingRestrictScalars aV).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingModuleDirectImage f SV SU cS).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm)
              (.up ℤ)).hom.app K) ≫
        chainDerivedUnit (proEtaleRingModuleDirectImage f RV RU cR)
          (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj K) := by
  let e := asIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)
  let b := (Functor.mapDerivedCategoryCompIso (proEtaleRingRestrictScalars aV)
    (proEtaleRingModulePullback f RV RU cR)) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback f SV SU cS)
        (proEtaleRingRestrictScalars aU)).symm
  have hb : (proEtaleRingRestrictionDerivedPullback
      f RV SV RU SU aV aU cR cS comm).inv = b.hom := by
    dsimp [proEtaleRingRestrictionDerivedPullback, b]
    rw [Category.assoc]
    rfl
  have h := derived_mate_factors (proEtaleRingModuleAdjunction f SV SU cS)
    (proEtaleRingModuleAdjunction f RV RU cR) e K
  dsimp only [e, asIso_hom] at h
  rw [restrictionPullback_mate f RV SV RU SU aV aU cR cS comm] at h
  rw [canonicalDerivedMate, hb]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedDirectImageComparison_unique
    {d d' : proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR}
    (hd : ∀ K : CochainComplex (proEtaleRingModules U SU) ℤ,
      (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
          (proEtaleRingDirectImageDerivedUnit f SV SU cS K) ≫
        d.hom.app (DerivedCategory.Q.obj K) ≫
        (proEtaleRingDerivedDirectImage f RV RU cR).map
          ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K) =
      (proEtaleRingRestrictScalars aV).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingModuleDirectImage f SV SU cS).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm)
              (.up ℤ)).hom.app K) ≫
        proEtaleRingDirectImageDerivedUnit f RV RU cR
          (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj K))
    (hd' : ∀ K : CochainComplex (proEtaleRingModules U SU) ℤ,
      (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
          (proEtaleRingDirectImageDerivedUnit f SV SU cS K) ≫
        d'.hom.app (DerivedCategory.Q.obj K) ≫
        (proEtaleRingDerivedDirectImage f RV RU cR).map
          ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K) =
      (proEtaleRingRestrictScalars aV).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingModuleDirectImage f SV SU cS).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm)
              (.up ℤ)).hom.app K) ≫
        proEtaleRingDirectImageDerivedUnit f RV RU cR
          (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj K)) :
    d = d' := by
  apply Iso.ext
  apply derived_comp_ext (proEtaleRingModuleDirectImage f SV SU cS)
    (proEtaleRingRestrictScalars aV)
    ((proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
      proEtaleRingDerivedDirectImage f RV RU cR)
  intro K
  dsimp only [chainDerivedUnit]
  have h := hd K
  have h' := hd' K
  dsimp only [proEtaleRingDirectImageDerivedUnit, chainDerivedUnit] at h h'
  apply (cancel_mono ((proEtaleRingDerivedDirectImage f RV RU cR).map
    ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K))).mp
  simpa only [Category.assoc] using h.trans h'.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Existence of the normalized derived direct-image comparison. -/
theorem proEtaleRingRestrictionDerivedDirectImage_exists :
    ∃ d : proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR,
      ∀ K : CochainComplex (proEtaleRingModules U SU) ℤ,
        (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
            (proEtaleRingDirectImageDerivedUnit f SV SU cS K) ≫
          d.hom.app (DerivedCategory.Q.obj K) ≫
          (proEtaleRingDerivedDirectImage f RV RU cR).map
            ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K) =
        (proEtaleRingRestrictScalars aV).mapDerivedCategoryFactors.hom.app
            (((proEtaleRingModuleDirectImage f SV SU cS).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm)
                (.up ℤ)).hom.app K) ≫
          proEtaleRingDirectImageDerivedUnit f RV RU cR
            (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj K) := by
  let m := canonicalDerivedMate f RV SV RU SU aV aU cR cS comm
  have hm := canonicalDerivedMate_factors f RV SV RU SU aV aU cR cS comm
  have hI (I : CochainComplex (proEtaleRingModules U SU) ℤ) [I.IsKInjective] :
      IsIso (m.app (DerivedCategory.Q.obj I)) := by
    obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj I)
    have : J.IsKInjective := hJ
    have : QuasiIso j := hj
    have : QuasiIso (((proEtaleRingModuleDirectImage f RV RU cR).mapHomologicalComplex
        (.up ℤ)).map j) := restriction_directImage_quasiIso f RV RU SU aU cR I J j
    have : IsIso (chainDerivedUnit (proEtaleRingModuleDirectImage f RV RU cR)
        (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj I)) :=
      chainDerivedUnit_isIso_of_resolution _ _ J j
    have : IsIso (chainDerivedUnit (proEtaleRingModuleDirectImage f SV SU cS) I) :=
      chainDerivedUnit_isIso _ I
    have hi := hm I
    have : IsIso
        ((proEtaleRingRestrictScalars aV).mapDerivedCategory.map
            (chainDerivedUnit (proEtaleRingModuleDirectImage f SV SU cS) I) ≫
          m.app (DerivedCategory.Q.obj I) ≫
          (proEtaleRingDerivedDirectImage f RV RU cR).map
            ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app I)) := by
      rw [hi]
      infer_instance
    have : IsIso (m.app (DerivedCategory.Q.obj I) ≫
        (proEtaleRingDerivedDirectImage f RV RU cR).map
          ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app I)) :=
      IsIso.of_isIso_comp_left
        ((proEtaleRingRestrictScalars aV).mapDerivedCategory.map
          (chainDerivedUnit (proEtaleRingModuleDirectImage f SV SU cS) I)) _
    exact IsIso.of_isIso_comp_right _
      ((proEtaleRingDerivedDirectImage f RV RU cR).map
        ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app I))
  have (X : DerivedCategory (proEtaleRingModules U SU)) : IsIso (m.app X) := by
    obtain ⟨I, hInj, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
    have : I.IsKInjective := hInj
    have : IsIso (m.app (DerivedCategory.Q.obj I)) := hI I
    have hn := m.naturality eI.hom
    have : IsIso (m.app X ≫
        ((proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
          proEtaleRingDerivedDirectImage f RV RU cR).map eI.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (((proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR).map eI.hom)
  have : IsIso m := NatIso.isIso_of_isIso_app _
  refine ⟨asIso m, ?_⟩
  intro K
  exact hm K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The direct-image comparison is the unique comparison compatible with the derived
units and the identity-on-sections underived comparison. -/
theorem proEtaleRingRestrictionDerivedDirectImage_existsUnique :
    ∃! d : proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR,
      ∀ K : CochainComplex (proEtaleRingModules U SU) ℤ,
        (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
            (proEtaleRingDirectImageDerivedUnit f SV SU cS K) ≫
          d.hom.app (DerivedCategory.Q.obj K) ≫
          (proEtaleRingDerivedDirectImage f RV RU cR).map
            ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K) =
        (proEtaleRingRestrictScalars aV).mapDerivedCategoryFactors.hom.app
            (((proEtaleRingModuleDirectImage f SV SU cS).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm)
                (.up ℤ)).hom.app K) ≫
      proEtaleRingDirectImageDerivedUnit f RV RU cR
            (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨d, hd⟩ := proEtaleRingRestrictionDerivedDirectImage_exists
    f RV SV RU SU aV aU cR cS comm
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  exact (derivedDirectImageComparison_unique f RV SV RU SU aV aU cR cS comm
    (d := d) (d' := d') hd hd').symm

/-- The canonical derived direct-image comparison `d`, determined by its unit normalization. -/
noncomputable def proEtaleRingRestrictionDerivedDirectImage :
    proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR :=
  Classical.choose
    (proEtaleRingRestrictionDerivedDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.style.haveILetI false in
/-- Exact restriction reflects derived isomorphisms, and the canonical coefficient
comparisons intertwine the canonical derived adjunctions. -/
theorem proEtaleRingSheafChangeAdjunction :
    (proEtaleRingRestrictScalars aU).mapDerivedCategory.ReflectsIsomorphisms ∧
    (proEtaleRingRestrictScalars aV).mapDerivedCategory.ReflectsIsomorphisms ∧
    ∀ (M : DerivedCategory (proEtaleRingModules V SV))
      (N : DerivedCategory (proEtaleRingModules U SU))
      (t : (proEtaleRingDerivedPullback f SV SU cS).obj M ⟶ N),
      (proEtaleRingDerivedAdjunction f RV RU cR).homEquiv _ _
          ((proEtaleRingRestrictionDerivedPullback
              f RV SV RU SU aV aU cR cS comm).inv.app M ≫
            (proEtaleRingRestrictScalars aU).mapDerivedCategory.map t) =
        (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
            ((proEtaleRingDerivedAdjunction f SV SU cS).homEquiv M N t) ≫
          (proEtaleRingRestrictionDerivedDirectImage
            f RV SV RU SU aV aU cR cS comm).hom.app N := by
  letI hU := (proEtaleRingRestrictScalars_properties aU).2.2
  letI hV := (proEtaleRingRestrictScalars_properties aV).2.2
  have hDerivedU :
      (proEtaleRingRestrictScalars aU).mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun g _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((proEtaleRingRestrictScalars aU).map
        ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff
        ((proEtaleRingRestrictScalars aU).mapDerivedCategoryHomologyFunctorIso n) g).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ (proEtaleRingRestrictScalars aU)
  have hDerivedV :
      (proEtaleRingRestrictScalars aV).mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun g _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((proEtaleRingRestrictScalars aV).map
        ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff
        ((proEtaleRingRestrictScalars aV).mapDerivedCategoryHomologyFunctorIso n) g).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ (proEtaleRingRestrictScalars aV)
  refine ⟨hDerivedU, hDerivedV, ?_⟩
  let m := canonicalDerivedMate f RV SV RU SU aV aU cR cS comm
  have hd : (proEtaleRingRestrictionDerivedDirectImage
      f RV SV RU SU aV aU cR cS comm).hom = m := by
    apply derived_comp_ext (proEtaleRingModuleDirectImage f SV SU cS)
      (proEtaleRingRestrictScalars aV)
      ((proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR)
    intro K
    apply (cancel_mono ((proEtaleRingDerivedDirectImage f RV RU cR).map
      ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K))).mp
    have hn := (Classical.choose_spec
      (proEtaleRingRestrictionDerivedDirectImage_existsUnique
        f RV SV RU SU aV aU cR cS comm)).1 K
    have hm := canonicalDerivedMate_factors f RV SV RU SU aV aU cR cS comm K
    simpa only [proEtaleRingDirectImageDerivedUnit, chainDerivedUnit,
      proEtaleRingRestrictionDerivedDirectImage, m, Category.assoc] using hn.trans hm.symm
  intro M N t
  rw [hd]
  dsimp only [m]
  rw [canonicalDerivedMate]
  exact mate_adjunct (proEtaleRingDerivedAdjunction f SV SU cS)
    (proEtaleRingDerivedAdjunction f RV RU cR)
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm).inv) M N t

end AlgebraicGeometry.Scheme
