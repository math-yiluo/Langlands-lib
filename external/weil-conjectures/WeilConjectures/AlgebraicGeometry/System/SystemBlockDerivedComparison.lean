/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import all WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import all WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import all Mathlib.AlgebraicGeometry.Pullbacks
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import all WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Category.ULift
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import all WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import all WeilConjectures.SixFunctors.BaseChange.DerivedForget
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import all WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange

/-! # Canonical comparisons for unbounded derived block functors

Source: Stacks Project, Tags 070I, 070Y, 08BJ and 09T5; Zheng Construction 4.1.
(blueprint: lem-pur-system-block-derived-comparisons).

This is the existing generic derived-comparison portion of SystemBlockRepetition,
extracted after coefficient-transport abstraction to keep each file within the
single-file compilation limit. All declarations and proofs retain their signatures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ u h w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

-- Elementary mate identities, proved locally to avoid depending on the geometric
-- normalization node. These proofs are the existing private mate calculations
-- from SectionDerivedPushpullNormalization (SHEAF group N9).
section DerivedComparison

variable {X : Type u₁} {Y : Type u₂} {Xd : Type u₃} {Yd : Type u₄}
  [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} Xd] [Category.{v₄} Yd]
  [Abelian X] [Abelian Y] [Abelian Xd] [Abelian Yd]
  [HasDerivedCategory.{w₁} X] [HasDerivedCategory.{w₂} Y]
  [HasDerivedCategory.{w₃} Xd] [HasDerivedCategory.{w₄} Yd]
  [Abelian.HasKInjectiveResolutions X] [Abelian.HasKInjectiveResolutions Xd]
  (RX : X ⥤ Xd) (RY : Y ⥤ Yd) (G : X ⥤ Y) (GD : Xd ⥤ Yd)
  [RX.Additive] [RY.Additive] [G.Additive] [GD.Additive]
  [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
  [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
  [RX.PreservesKInjectiveComplexes]

/-- The canonical comparison of total right derived functors, constructed from their
universal properties. In the system application the supplied square is identity on
sections, morphisms and transitions, so this is kappa_t of the node.
Source: Zheng 4.1 and paragraph before 4.10; Stacks 070Y
(blueprint: lem-pur-system-block-derived-comparisons). -/
def blockDerivedComparison (square : RX ⋙ GD ≅ G ⋙ RY) :
    RX.mapDerivedCategory ⋙ GD.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ RY.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIso RX GD).symm ≪≫
    Functor.rightDerivedFunctorNatIso square ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso G RY

private theorem homotopyCompInv
    {A : Type*} {B : Type*} {D : Type*}
    [Category A] [Category B] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive D]
    (F : A ⥤ B) (H : B ⥤ D) [F.Additive] [H.Additive]
    (K : HomotopyCategory A (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).inv.app K = 𝟙 _ := by
  have h := (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).hom_inv_id_app K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
  exact h

private theorem comparisonFac (square : RX ⋙ GD ≅ G ⋙ RY)
    (K : HomotopyCategory X (.up ℤ)) :
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit RX GD).app K ≫
        (blockDerivedComparison RX RY G GD square).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory square.hom (.up ℤ)).app K) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit G RY).app K := by
  simp only [blockDerivedComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app RX GD K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc]
  rw [show (RX ⋙ GD).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso square).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory square.hom (.up ℤ)).app K) ≫
        (G ⋙ RY).rightDerivedFunctorUnit.app K by
    exact Functor.rightDerivedNatTrans_app _ _ _ _
      (HomotopyCategory.quasiIso X (.up ℤ)) _ K]
  simp only [Category.assoc]
  congr 1
  simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso]

attribute [local irreducible] blockDerivedComparison

section InverseComparison
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : C ⥤ D) (R : A ⥤ C) (S : B ⥤ D)
  [F.Additive] [G.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [R.PreservesKInjectiveComplexes]

private def derived_square (e : F ⋙ S ≅ R ⋙ G) :
    F.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅
      R.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (blockDerivedComparison R S F G e.symm).symm

private theorem square_fac (e : F ⋙ S ≅ R ⋙ G)
    (K : HomotopyCategory A (.up ℤ)) :
    S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
        (derived_square F G R S e).hom.app (DerivedCategory.Qh.obj K) =
      S.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        G.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (R.mapDerivedCategoryFactorsh.inv.app K) := by
  have hf := comparisonFac R S F G e.symm K
  simp only [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, homotopyCompInv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Iso.symm_hom, Category.assoc] at hf
  erw [Category.id_comp] at hf
  apply (cancel_mono ((blockDerivedComparison R S F G e.symm).hom.app
    (DerivedCategory.Qh.obj K))).mp
  simp only [derived_square, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
  erw [hf]
  simp only [← DerivedCategory.Qh.map_comp_assoc, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  erw [DerivedCategory.Qh.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  erw [Category.comp_id]
end InverseComparison

section Canonical
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : C ⥤ D) (R : A ⥤ C) (S : B ⥤ D)
  [F.Additive] [G.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

end Canonical

end DerivedComparison
section CoefficientComparison

variable {X : Type u₁} {Y : Type u₂} {Xp : Type u₃} {Yp : Type u₄}
  [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} Xp] [Category.{v₄} Yp]
  [Abelian X] [Abelian Y] [Abelian Xp] [Abelian Yp]
  [HasDerivedCategory.{w₁} X] [HasDerivedCategory.{w₂} Y]
  [HasDerivedCategory.{w₃} Xp] [HasDerivedCategory.{w₄} Yp]
  [Abelian.HasKInjectiveResolutions X] [Abelian.HasKInjectiveResolutions Xp]
  (UX : Xp ⥤ X) (UY : Yp ⥤ Y) (G : X ⥤ Y) (Gp : Xp ⥤ Yp)
  [UX.Additive] [UY.Additive] [G.Additive] [Gp.Additive]
  [PreservesFiniteLimits UX] [PreservesFiniteColimits UX]
  [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]

end CoefficientComparison
section Canonical
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : C ⥤ D) (R : A ⥤ C) (S : B ⥤ D)
  [F.Additive] [G.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

end Canonical

section CoefficientNaturality

variable {X Y Xd Yd Xp Yp Xdp Ydp : Type u}
  [Category.{h} X] [Category.{h} Y] [Category.{h} Xd] [Category.{h} Yd]
  [Category.{h} Xp] [Category.{h} Yp] [Category.{h} Xdp] [Category.{h} Ydp]
  [Abelian X] [Abelian Y] [Abelian Xd] [Abelian Yd]
  [Abelian Xp] [Abelian Yp] [Abelian Xdp] [Abelian Ydp]
  [HasDerivedCategory.{w} X] [HasDerivedCategory.{w} Y]
  [HasDerivedCategory.{w} Xd] [HasDerivedCategory.{w} Yd]
  [HasDerivedCategory.{w} Xp] [HasDerivedCategory.{w} Yp]
  [HasDerivedCategory.{w} Xdp] [HasDerivedCategory.{w} Ydp]
  [Abelian.HasKInjectiveResolutions X] [Abelian.HasKInjectiveResolutions Xd]
  [Abelian.HasKInjectiveResolutions Xp] [Abelian.HasKInjectiveResolutions Xdp]
  (RX : X ⥤ Xd) (RY : Y ⥤ Yd) (RXp : Xp ⥤ Xdp) (RYp : Yp ⥤ Ydp)
  (UX : Xp ⥤ X) (UY : Yp ⥤ Y) (UXd : Xdp ⥤ Xd) (UYd : Ydp ⥤ Yd)
  (G : X ⥤ Y) (GD : Xd ⥤ Yd) (Gp : Xp ⥤ Yp) (GDp : Xdp ⥤ Ydp)
  [RX.Additive] [RY.Additive] [RXp.Additive] [RYp.Additive]
  [UX.Additive] [UY.Additive] [UXd.Additive] [UYd.Additive]
  [G.Additive] [GD.Additive] [Gp.Additive] [GDp.Additive]
  [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
  [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
  [PreservesFiniteLimits RXp] [PreservesFiniteColimits RXp]
  [PreservesFiniteLimits RYp] [PreservesFiniteColimits RYp]
  [PreservesFiniteLimits UX] [PreservesFiniteColimits UX]
  [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]
  [PreservesFiniteLimits UXd] [PreservesFiniteColimits UXd]
  [PreservesFiniteLimits UYd] [PreservesFiniteColimits UYd]
  [RX.PreservesKInjectiveComplexes] [RXp.PreservesKInjectiveComplexes]

end CoefficientNaturality

section ExactComposition
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private noncomputable def exact_comp (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso F G ≪≫
    Functor.mapDerivedCategoryNatIso e

end ExactComposition

section HorizontalComposition
variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  [Abelian A] [Abelian B] [Abelian C] [Abelian A'] [Abelian B'] [Abelian C']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ A') (G : B ⥤ B') (H : C ⥤ C')
  (R : A ⥤ B) (S : B ⥤ C) (T : A ⥤ C)
  (R' : A' ⥤ B') (S' : B' ⥤ C') (T' : A' ⥤ C')
  [F.Additive] [G.Additive] [H.Additive]
  [R.Additive] [S.Additive] [T.Additive] [R'.Additive] [S'.Additive] [T'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
  [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
  [R.PreservesKInjectiveComplexes] [S.PreservesKInjectiveComplexes]
  [T.PreservesKInjectiveComplexes]
  (e : F ⋙ R' ≅ R ⋙ G) (d : G ⋙ S' ≅ S ⋙ H) (c : F ⋙ T' ≅ T ⋙ H)
  (r : R ⋙ S ≅ T) (s : R' ⋙ S' ≅ T')

-- Localization reduces coherence of these canonical squares to the ordinary identity.
end HorizontalComposition

section Composition

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type u}
  [Category.{h} X₀] [Category.{h} X₁] [Category.{h} X₂]
  [Category.{h} Y₀] [Category.{h} Y₁] [Category.{h} Y₂]
  [Abelian X₀] [Abelian X₁] [Abelian X₂]
  [Abelian Y₀] [Abelian Y₁] [Abelian Y₂]
  [HasDerivedCategory.{w} X₀] [HasDerivedCategory.{w} X₁] [HasDerivedCategory.{w} X₂]
  [HasDerivedCategory.{w} Y₀] [HasDerivedCategory.{w} Y₁] [HasDerivedCategory.{w} Y₂]
  [Abelian.HasKInjectiveResolutions X₀] [Abelian.HasKInjectiveResolutions X₁]
  [Abelian.HasKInjectiveResolutions X₂]
  (RX₀₁ : X₀ ⥤ X₁) (RX₁₂ : X₁ ⥤ X₂) (RX₀₂ : X₀ ⥤ X₂)
  (RY₀₁ : Y₀ ⥤ Y₁) (RY₁₂ : Y₁ ⥤ Y₂) (RY₀₂ : Y₀ ⥤ Y₂)
  (G₀ : X₀ ⥤ Y₀) (G₁ : X₁ ⥤ Y₁) (G₂ : X₂ ⥤ Y₂)
  [RX₀₁.Additive] [RX₁₂.Additive] [RX₀₂.Additive]
  [RY₀₁.Additive] [RY₁₂.Additive] [RY₀₂.Additive]
  [G₀.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits RX₀₁] [PreservesFiniteColimits RX₀₁]
  [PreservesFiniteLimits RX₁₂] [PreservesFiniteColimits RX₁₂]
  [PreservesFiniteLimits RX₀₂] [PreservesFiniteColimits RX₀₂]
  [PreservesFiniteLimits RY₀₁] [PreservesFiniteColimits RY₀₁]
  [PreservesFiniteLimits RY₁₂] [PreservesFiniteColimits RY₁₂]
  [PreservesFiniteLimits RY₀₂] [PreservesFiniteColimits RY₀₂]
  [RX₀₁.PreservesKInjectiveComplexes] [RX₁₂.PreservesKInjectiveComplexes]
  [RX₀₂.PreservesKInjectiveComplexes]

end Composition

section Identity

variable {X Y : Type u} [Category.{h} X] [Category.{h} Y] [Abelian X] [Abelian Y]
  [HasDerivedCategory.{w} X] [HasDerivedCategory.{w} Y]
  [Abelian.HasKInjectiveResolutions X]
  (RX : X ⥤ X) (RY : Y ⥤ Y) (G : X ⥤ Y)
  [RX.Additive] [RY.Additive] [G.Additive]
  [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
  [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
  [RX.PreservesKInjectiveComplexes]

end Identity

end WeilConjectures.SemilinearSections
