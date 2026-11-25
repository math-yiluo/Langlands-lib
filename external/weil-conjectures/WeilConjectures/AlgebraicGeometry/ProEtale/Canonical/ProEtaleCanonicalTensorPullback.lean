/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement

/-!
# Canonical tensor pullback on the small pro-etale site

The object universe of the site is u+1 and its morphism universe is u.

## References

* Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E
* Modules on Sites, Tag 03EL
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf
  CategoryTheory.tensorPullbackTotal CategoryTheory.tensorPullbackTotalComponent

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem tensor_hom_ext (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M N H : proEtaleRingModules X R}
    (a b : ((proEtaleOrdinaryTensor X R).obj M).obj N ⟶ H)
    (h : ∀ (U : X.ProEtᵒᵖ) (m : M.val.obj U) (n : N.val.obj U),
      a.val.app U (proEtaleTensorPair X R M N U m n) =
        b.val.app U (proEtaleTensorPair X R M N U m n)) : a = b := by
  exact modelTensor_hom_ext X R a b h

private noncomputable def normalizedAlgebraicLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    SheafOfModules.AlgebraicInverseImage
      (proEtaleSheafInverseImage f (Type (u + 1))) R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  modelNormalizedAlgebraicLift f R

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

attribute [local irreducible] proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso
  proEtaleRingDerivedPullbackFactors HomologicalComplex₂.total
  CategoryTheory.Functor.mapBifunctorHomologicalComplex

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

/-- Pullback preserves flat K-flat representatives and has a unique canonical tensor comparison. -/
theorem proEtaleCanonicalTensorPullback
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S) :
    (∀ P : CochainComplex (proEtaleRingModules Y R) ℤ,
      proEtaleFlatRepresentatives Y R P →
        proEtaleFlatRepresentatives X S
          (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ∧
    ∃! alpha : a.tensor ⋙ proEtaleRingDerivedPullback f R S c ≅
      ((proEtaleRingDerivedPullback f R S c).prod
        (proEtaleRingDerivedPullback f R S c)) ⋙ b.tensor,
      ∀ (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
        (hp : proEtaleFlatRepresentatives Y R P) (hq : proEtaleFlatRepresentatives Y R Q),
        ∃ (hp' : proEtaleFlatRepresentatives X S
            (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))
          (hq' : proEtaleFlatRepresentatives X S
            (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Q)),
          (proEtaleRingDerivedPullback f R S c).map
              (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
            alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            b.tensor.map (Prod.mkHom
              ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
              ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) =
          (proEtaleRingDerivedPullbackFactors f R S c).hom.app
              (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor Y R)) ≫
            (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P Q)).inv ≫
            b.representative.hom.app
              (⟨_, hp'⟩, ⟨_, hq'⟩) := by
  classical
  let A := proEtaleRingModules Y R
  let B := proEtaleRingModules X S
  let L := proEtaleRingModulePullback f R S c
  let F := L.mapHomologicalComplex (.up ℤ)
  let LF := proEtaleRingDerivedPullback f R S c
  let PR := proEtaleFlatRepresentatives Y R
  let PS := proEtaleFlatRepresentatives X S
  let tR := Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let tS := Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  obtain ⟨hF, ⟨ff'⟩, b0, hb0⟩ := proEtaleTensorPullbackDescentData f R S c
  obtain ⟨alpha, ha, hu⟩ := CategoryTheory.tensorComparisonDescent
    (K := CochainComplex A ℤ) (H := CochainComplex B ℤ)
    (D := DerivedCategory A) (E := DerivedCategory B)
    DerivedCategory.Q DerivedCategory.Q F LF (proEtaleRingDerivedPullbackFactors f R S c).hom
    PR PS hF ff' tR tS a.tensor b.tensor a.representative b.representative b0.symm
    (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  have hb (P Q : CochainComplex A ℤ) :
      DerivedCategory.Q.map (b0.symm.hom.app (P, Q)) =
        (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P Q)).inv := by
    exact congrArg DerivedCategory.Q.map (hb0 P Q)
  refine ⟨hF, alpha, ?_, ?_⟩
  · intro P Q hp hq
    refine ⟨hF P hp, hF Q hq, ?_⟩
    have hh := ha P Q hp hq
    simp only [hb] at hh
    dsimp only [tR, Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex] at hh
    exact hh
  · intro alpha' ha'
    apply hu alpha'
    intro P Q hp hq
    obtain ⟨hp', hq', hh⟩ := ha' P Q hp hq
    simp only [hb]
    dsimp only [tR, Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex]
    exact hh

/-- The unique derived comparison specified on every flat K-flat pair, rather than an
arbitrary natural isomorphism. -/
noncomputable def proEtaleCanonicalTensorComparison
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S) :=
  Classical.choose (proEtaleCanonicalTensorPullback f R S c a b).2.exists

end AlgebraicGeometry.Scheme
