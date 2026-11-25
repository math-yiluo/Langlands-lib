/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.PulledReduction.PulledReductionStrictTowerComparison
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
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
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
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
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Homology.ScalarDescent.IntegralLisseReductionScalarDescent
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement

/-! # Successive normalizations of the pulled reduction comparison

All quotient indices are zero based: `n` denotes the positive exponent `n + 1`.
The maps retain the finite coefficient action and the universal computation counits.

## References

* Stacks 0D6D, 07A4
* Stacks 06YY, 03EL
* Stacks 03EL, 0D6D and 0G7E
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u v r w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient

-- Prefer concrete module categories to reverse inference through an abstract tensor corner.
attribute [local instance 0] SheafOfModules.RingedTensorCorner.category
  SheafOfModules.RingedTensorCorner.derived

private theorem identityNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (X Y : C) (f : (𝟭 C).obj X ⟶ Y) :
    (Adjunction.id (C := D)).homEquiv (F.obj X) (F.obj Y)
        (𝟙 (F.obj X) ≫ F.map f) =
      F.map ((Adjunction.id (C := C)).homEquiv X Y f) ≫ 𝟙 (F.obj Y) := by
  simp only [Adjunction.id, Functor.id_obj]
  change (𝟙 _ ≫ 𝟙 _ ≫ F.map f) = F.map (𝟙 _ ≫ f) ≫ 𝟙 _
  rw [Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]

private theorem ordinaryMateTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (L₁ : C ⥤ D) (R₁ : D ⥤ C) (L₂ : E ⥤ F) (R₂ : F ⥤ E)
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (G : C ⥤ E) (H : D ⥤ F)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (M : C) :
    adj₂.homEquiv (G.obj M) (H.obj (L₁.obj M))
        (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ β)).app M) =
      G.map (adj₁.unit.app M) ≫ β.app (L₁.obj M) := by
  exact (unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ β) M).symm

private theorem cochainTranspose
    {C D E F : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] [Preadditive E] [Category F] [Preadditive F]
    (L₁ : C ⥤ D) (R₁ : D ⥤ C) (L₂ : E ⥤ F) (R₂ : F ⥤ E)
    (G : C ⥤ E) (H : D ⥤ F)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (ι : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (hι : ∀ M, adj₂.homEquiv _ _ (ι.app M) =
      G.map (adj₁.unit.app M) ≫ β.app (L₁.obj M))
    (P : CochainComplex C ℤ) :
    (adj₂.mapHomologicalComplex (.up ℤ)).homEquiv
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((H.mapHomologicalComplex (.up ℤ)).obj
          ((L₁.mapHomologicalComplex (.up ℤ)).obj P))
        ((ι.mapHomologicalComplex (.up ℤ)).app P) =
      (G.mapHomologicalComplex (.up ℤ)).map
        ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (β.mapHomologicalComplex (.up ℤ)).app
        ((L₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact hι (P.X i)

private theorem exactMateRepresentative
    {C D E F : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [Category E] [Abelian E] [HasDerivedCategory E]
    [Category F] [Abelian F] [HasDerivedCategory F]
    (L₁ : C ⥤ D) (R₁ : D ⥤ C) (L₂ : E ⥤ F) (R₂ : F ⥤ E)
    (G : C ⥤ E) (H : D ⥤ F)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (LD₁ : DerivedCategory C ⥤ DerivedCategory D)
    (LD₂ : DerivedCategory E ⥤ DerivedCategory F)
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (ad₁ : LD₁ ⊣ R₁.mapDerivedCategory) (ad₂ : LD₂ ⊣ R₂.mapDerivedCategory)
    (ε₁ : DerivedCategory.Q ⋙ LD₁ ⟶ L₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε₂ : DerivedCategory.Q ⋙ LD₂ ⟶ L₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (e₁ : ∀ P : CochainComplex C ℤ, LD₁.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L₁.mapHomologicalComplex (.up ℤ)).obj P))
    (e₂ : ∀ P : CochainComplex E ℤ, LD₂.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L₂.mapHomologicalComplex (.up ℤ)).obj P))
    (he₁ : ∀ P, ε₁.app P = e₁ P) (he₂ : ∀ P, ε₂.app P = e₂ P)
    (h₁ : ∀ P K (f : (L₁.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad₁.homEquiv _ _ (e₁ P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a₁.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          R₁.mapDerivedCategoryFactors.inv.app K)
    (h₂ : ∀ P K (f : (L₂.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad₂.homEquiv _ _ (e₂ P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a₂.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          R₂.mapDerivedCategoryFactors.inv.app K)
    (β : R₁ ⋙ G ≅ H ⋙ R₂)
    (βD : R₁.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R₂.mapDerivedCategory)
    (hβD : βD = (Functor.mapDerivedCategorySquareIso β).hom)
    (ι : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (hι : ι = ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ β.hom)))
    (μ : G.mapDerivedCategory ⋙ LD₂ ⟶ LD₁ ⋙ H.mapDerivedCategory)
    (hμ : μ = ((mateEquiv ad₁ ad₂).symm (TwoSquare.mk _ _ _ _ βD)))
    (P : CochainComplex C ℤ) :
    μ.app (DerivedCategory.Q.obj P) ≫ H.mapDerivedCategory.map (e₁ P) ≫
        H.mapDerivedCategoryFactors.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj P) =
      LD₂.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        e₂ ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((ι.mapHomologicalComplex (.up ℤ)).app P) := by
  subst μ
  have ht (K : CochainComplex D ℤ) := Functor.exactSquare_fac β K
  have hi (M : C) : a₂.homEquiv _ _ (ι.app M) =
      G.map (a₁.unit.app M) ≫ β.hom.app (L₁.obj M) := by
    rw [hι]
    exact ordinaryMateTranspose L₁ R₁ L₂ R₂ a₁ a₂ G H β.hom M
  have hc := cochainTranspose L₁ R₁ L₂ R₂ G H a₁ a₂ β.hom ι hi
  have hh := CategoryTheory.derivedMate_comparison
    (L₁ := L₁.mapHomologicalComplex (.up ℤ))
    (R₁ := R₁.mapHomologicalComplex (.up ℤ))
    (L₂ := L₂.mapHomologicalComplex (.up ℤ))
    (R₂ := R₂.mapHomologicalComplex (.up ℤ))
    (LD₁ := LD₁) (LD₂ := LD₂)
    (RD₁ := R₁.mapDerivedCategory) (RD₂ := R₂.mapDerivedCategory)
    (G := G.mapHomologicalComplex (.up ℤ)) (H := H.mapHomologicalComplex (.up ℤ))
    (GD := G.mapDerivedCategory) (HD := H.mapDerivedCategory)
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
    (QC := DerivedCategory.Q) (QD := DerivedCategory.Q)
    (a₁.mapHomologicalComplex (.up ℤ)) (a₂.mapHomologicalComplex (.up ℤ)) ad₁ ad₂
    ε₁ ε₂ R₁.mapDerivedCategoryFactors R₂.mapDerivedCategoryFactors
    G.mapDerivedCategoryFactors H.mapDerivedCategoryFactors
    (by intro Q K f; rw [he₁]; exact h₁ Q K f)
    (by intro Q K f; rw [he₂]; exact h₂ Q K f)
    (TwoSquare.mk _ _ _ _ (β.hom.mapHomologicalComplex (.up ℤ)))
    (TwoSquare.mk _ _ _ _ βD)
    (by intro K; rw [hβD]; exact ht K)
    (ι.mapHomologicalComplex (.up ℤ)) hc P
  rw [he₁, he₂] at hh
  exact hh

private theorem squareOfRepresentatives
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {N H B B' : C} {N' H' A A' K K' : D}
    (τ : N ⟶ H) (σ : N' ⟶ H')
    (θN : F.obj N ⟶ N') (θH : F.obj H ⟶ H')
    (n : N ⟶ B) (h : H ⟶ B') (n' : N' ⟶ A) (h' : H' ⟶ A') [Mono h']
    (c : F.obj B ⟶ K) (c' : F.obj B' ⟶ K')
    (t : B ⟶ B') (s : A ⟶ A') (q : K ⟶ A) (q' : K' ⟶ A') (u : K ⟶ K')
    (hτ : τ ≫ h = n ≫ t) (hσ : σ ≫ h' = n' ≫ s)
    (hθN : θN ≫ n' = F.map n ≫ c ≫ q)
    (hθH : θH ≫ h' = F.map h ≫ c' ≫ q')
    (hc : F.map t ≫ c' = c ≫ u) (hq : u ≫ q' = q ≫ s) :
    F.map τ ≫ θH = θN ≫ σ := by
  apply (cancel_mono h').1
  simp only [Category.assoc]
  rw [hθH, hσ]
  rw [← F.map_comp_assoc, hτ]
  simp only [F.map_comp, Category.assoc]
  rw [reassoc_of% hc, hq]
  rw [← Category.assoc θN n', hθN]
  simp only [Category.assoc]

private theorem normalizedMate_app
    {B C D E F : Type*} [Category B] [Category C] [Category D]
    [Category E] [Category F]
    (L : B ⥤ C) (G : C ⥤ D) (H : E ⥤ F) (S : C ⥤ E) (T : D ⥤ F) (R : B ⥤ E)
    (μ : G ⋙ T ⟶ S ⋙ H) (ν : L ⋙ S ⟶ R) (X : B) :
    ((Functor.associator L G T).hom ≫ Functor.whiskerLeft L μ ≫
      (Functor.associator L S H).inv ≫ Functor.whiskerRight ν H).app X =
        μ.app (L.obj X) ≫ H.map (ν.app X) := by
  simp only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp]

private def normalizedMateIso
    {B C D E F : Type*} [Category B] [Category C] [Category D]
    [Category E] [Category F]
    (L : B ⥤ C) (G : C ⥤ D) (H : E ⥤ F) (S : C ⥤ E) (T : D ⥤ F) (R : B ⥤ E)
    (μ : G ⋙ T ≅ S ⋙ H) (ν : L ⋙ S ≅ R) : (L ⋙ G) ⋙ T ≅ R ⋙ H :=
  NatIso.ofComponents (fun X ↦ μ.app (L.obj X) ≪≫ H.mapIso (ν.app X)) (by
    intro X Y f
    have hh := (Functor.associator L G T ≪≫ Functor.isoWhiskerLeft L μ ≪≫
      (Functor.associator L S H).symm ≪≫ Functor.isoWhiskerRight ν H).hom.naturality f
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Iso.app_hom, Functor.mapIso_hom] using hh)

private theorem mateRepresentativeComposition
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (G : C ⥤ D) (H : E ⥤ F) (S : C ⥤ E) (T : D ⥤ F)
    (μ : G ⋙ T ⟶ S ⋙ H)
    {x y : C} {z v w : E} {u : D} {v' w' u' : F}
    (ε : x ⟶ y) (ν : S.obj x ⟶ z) (εa : z ⟶ w)
    (εq : S.obj y ⟶ v) (bal : v ⟶ w)
    (fb : G.obj y ⟶ u) (fa : H.obj w ⟶ w') (fq : H.obj v ⟶ v')
    (cc : T.obj u ⟶ u') (m : u' ⟶ v') (b : v' ⟶ w') (mb : u' ⟶ w')
    (hν : ν ≫ εa = S.map ε ≫ εq ≫ bal)
    (hbal : H.map bal ≫ fa = fq ≫ b)
    (hm : μ.app y ≫ H.map εq ≫ fq = T.map fb ≫ cc ≫ m)
    (hmb : m ≫ b = mb)
    (θ : T.obj (G.obj x) ⟶ H.obj z) (ha : H.obj z ⟶ w') (hb : G.obj x ⟶ u)
    (eθ : θ = μ.app x ≫ H.map ν) (ea : ha = H.map εa ≫ fa)
    (eb : hb = G.map ε ≫ fb) :
    θ ≫ ha = T.map hb ≫ cc ≫ mb := by
  rw [eθ, ea, eb]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hν]
  simp only [H.map_comp, Category.assoc]
  rw [← reassoc_of% μ.naturality ε]
  rw [hbal, reassoc_of% hm]
  simp only [T.map_comp, Category.assoc]
  rw [hmb]

private theorem map_comp_of_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (e : f ≫ g = h) :
    F.map f ≫ F.map g = F.map h :=
  (F.map_comp f g).symm.trans (congrArg (fun k : x ⟶ z ↦ F.map k) e)

private theorem map_square_of_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z w : C} (f : x ⟶ y) (g : y ⟶ w) (h : x ⟶ z) (k : z ⟶ w)
    (e : f ≫ g = h ≫ k) : F.map f ≫ F.map g = F.map h ≫ F.map k :=
  (map_comp_of_eq F f g (h ≫ k) e).trans (F.map_comp h k)

private theorem complexSquare
    {A B C D : Type*} [Category A] [Preadditive A] [Category B] [Preadditive B]
    [Category C] [Preadditive C] [Category D] [Preadditive D]
    (U : A ⥤ B) (Cb : B ⥤ C) (Ca : B ⥤ D) (Hb : A ⥤ C) (Ha : A ⥤ D) (F : C ⥤ D)
    [U.Additive] [Cb.Additive] [Ca.Additive] [Hb.Additive] [Ha.Additive] [F.Additive]
    (δ : Cb ⋙ F ⟶ Ca) (τb : U ⋙ Cb ⟶ Hb) (τa : U ⋙ Ca ⟶ Ha) (θ : Hb ⋙ F ⟶ Ha)
    (hs : ∀ M, F.map (τb.app M) ≫ θ.app M = δ.app (U.obj M) ≫ τa.app M)
    (P : CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        ((τb.mapHomologicalComplex (.up ℤ)).app P) ≫
      (θ.mapHomologicalComplex (.up ℤ)).app P =
    (δ.mapHomologicalComplex (.up ℤ)).app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (τa.mapHomologicalComplex (.up ℤ)).app P := by
  apply HomologicalComplex.hom_ext
  intro i
  exact hs (P.X i)

private theorem transportedIso_eq
    {I C D : Type*} [Category C] [Category D]
    (F : I → (C ⥤ D)) {a b : I} (G : C ⥤ D) (e : G ≅ F a) (h : a = b) :
    Eq.ndrec (motive := fun z ↦ G ≅ F z) e h = e ≪≫ eqToIso (congrArg F h) := by
  subst b
  simp only [eqToIso_refl, Iso.trans_refl]

private theorem whiskeredIso_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) {F G : D ⥤ E} (e : F ≅ G) (K : C) :
    (Functor.isoWhiskerLeft L e).hom.app K = e.hom.app (L.obj K) := rfl

private theorem compositorRepresentative
    {C D E : Type*} [Category C] [Category D] [Category E]
    (A : C ⥤ D) (B : D ⥤ E) (F : C ⥤ E) (e : A ⋙ B ⟶ F)
    {x y : C} (ε : x ⟶ y) {u : D} {v w : E}
    (a : A.obj y ⟶ u) (b : B.obj u ⟶ v) (n : v ⟶ w) (c : F.obj y ⟶ w)
    (h : e.app y ≫ c = B.map a ≫ b ≫ n)
    (θ : B.obj (A.obj x) ⟶ F.obj x) (na : F.obj x ⟶ w) (nb : A.obj x ⟶ u)
    (eθ : θ = e.app x) (ea : na = F.map ε ≫ c) (eb : nb = A.map ε ≫ a) :
    θ ≫ na = B.map nb ≫ b ≫ n := by
  rw [eθ, ea, eb]
  rw [← reassoc_of% e.naturality ε, h]
  simp only [Functor.map_comp, Category.assoc]

private theorem unitOfRepresentative
    {C : Type*} [Category C] (F : C ⥤ C) (η : F ⟶ 𝟭 C)
    {X Y Z : C} (h : X ⟶ Y) [Mono h] (θ : F.obj X ⟶ X)
    (c : F.obj Y ⟶ Z) (u : Z ⟶ Y)
    (hθ : θ ≫ h = F.map h ≫ c ≫ u) (hη : η.app Y = c ≫ u) :
    θ = η.app X := by
  apply (cancel_mono h).1
  rw [hθ, ← hη]
  exact η.naturality h

namespace AlgebraicGeometry.Scheme.PulledNormalization

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The existing scalar extension with its universal presentation, on the original site. -/
def scalarPresentation (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S) :
    Presentation.{t + 1, t, t + 1, t + 2} a where
  ordinary := reductionChange T a
  obj_eq := (reductionChangeExistence T a).choose_spec.choose
  map_eq := (reductionChangeExistence T a).choose_spec.choose_spec.choose
  additive := reductionChangeAdditive T a
  derived := reductionDerivedChange T a
  counit := reductionDerivedCounit T a
  universal := reductionDerivedUniversal T a

attribute [local irreducible] Functor.mapDerivedCategory

/-- Finite inverse image with the specified finite coefficient identification. -/
abbrev finitePull (n : ℕ) :=
  proEtaleRingModulePullback g (d.finiteRing Y n) (d.finiteRing X n) (d.finiteRingIso g n)

/-- The functor whose value is H_n, before forgetting the quotient action. -/
def H (n : ℕ) := d.reduction Y n ⋙ (finitePull d g n).mapDerivedCategory

/-- The functor whose value is N_n, for arbitrary ambient completed inputs. -/
def N (n : ℕ) := PulledReduction.source d g ⋙
  reductionDerivedChange X (OrderedExchange.quotient d X n)

/-- The actual pulled finite complex functor, on modules in each cochain degree. -/
abbrev ordinaryH (n : ℕ) := reductionChange Y (d.projection Y n) ⋙ finitePull d g n

/-- The canonical comparison from H_n on a representative to the ordinary pulled complex. -/
def hCounit (n : ℕ) (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    (H d g n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ordinaryH d g n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (finitePull d g n).mapDerivedCategory.map
      (reductionScalarComplexCounit Y (d.projection Y n) P) ≫
    (finitePull d g n).mapDerivedCategoryFactors.hom.app
      ((reductionChangeComplex Y (d.projection Y n)).obj P)

/-- The coefficient associativity equality for constant reduction. -/
abbrev quotientComp (T : Scheme.{t}) (b a : ℕ) (h : a ≤ b) :
    OrderedExchange.quotient d T b ≫ reductionCoefficientMap T d b a h =
      OrderedExchange.quotient d T a :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f ↦ exchangeScalar d T ≫ f)
      (completedReductionProjection_comp T d b a h))

/-- The recorded normalization interface, with the coefficient sheafification
and locally-bijective comparison specified at the existing coefficient universe. -/
abbrev ScalarNormalization (T : Scheme.{t}) :=
  @Normalization.{t + 1, t, t + 1, t + 2} T.ProEt inferInstance
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) inferInstance
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
    (WeilConjectures.integralCoefficientAbSheafify.{t, t} T)
    (fun R ↦ reductionModulesHasDerivedCategory T R)
    (fun {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
      (a : R ⟶ S) ↦ scalarPresentation.{t} T a)

private theorem tensor_balance (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ)
    (r : R.obj.obj U) (s : S.obj.obj U) (x : M.val.obj U) :
    reductionTensorSection T a M U s (r • x) =
      (a.hom.app U r * s) • reductionTensorSection T a M U 1 x := by
  have h := ((reductionUnit T a M).val.app U).hom.map_smul r x
  with_unfolding_all
    change
      (reductionUnit T a M).val.app U (r • x) =
        a.hom.app U r •
          (show ((reductionChange T a).obj M).val.obj U from
            (reductionUnit T a M).val.app U x) at h
  rw [reductionUnit_apply, reductionUnit_apply] at h
  calc
    reductionTensorSection T a M U s (r • x) =
        s • reductionTensorSection T a M U 1 (r • x) := by
      simpa only [mul_one] using (tensorSection_smul T a M U s 1 (r • x)).symm
    _ = s • (a.hom.app U r • reductionTensorSection T a M U 1 x) := congrArg (s • ·) h
    _ = _ := by rw [smul_smul, mul_comm s]

/-- The existing normalized derived scalar associator with explicit site instances. -/
def scalarAssoc (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S) (b : S ⟶ V) :
    reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅
      reductionDerivedChange T (a ≫ b) :=
  @Normalization.derived.{t + 1, t, t + 1, t + 2} T.ProEt inferInstance
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) inferInstance
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
    (WeilConjectures.integralCoefficientAbSheafify.{t, t} T)
    (fun U ↦ reductionModulesHasDerivedCategory T U)
    (fun {U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
      (f : U ⟶ V) ↦ scalarPresentation.{t} T f) nrm R S V a b

attribute [local irreducible] pbcScalarAdjunction pbcDerivedScalarAdjunction

private def ordinaryAssoc (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S) (b : S ⟶ V) :
    reductionChange T a ⋙ reductionChange T b ≅ reductionChange T (a ≫ b) :=
  @Normalization.ordinary.{t + 1, t, t + 1, t + 2} T.ProEt inferInstance
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) inferInstance
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
    (WeilConjectures.integralCoefficientAbSheafify.{t, t} T)
    (fun U ↦ reductionModulesHasDerivedCategory T U)
    (fun {U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
      (f : U ⟶ V) ↦ scalarPresentation T f) nrm R S V a b

private theorem ordinaryAssoc_formula (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S) (b : S ⟶ V)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U)
    (s : S.obj.obj U) (v : V.obj.obj U) :
    ((ordinaryAssoc T nrm a b).hom.app M).val.app U
      (reductionTensorSection T b ((reductionChange T a).obj M) U v
        (reductionTensorSection T a M U s x)) =
      reductionTensorSection T (a ≫ b) M U (b.hom.app U s * v) x := by
  have hh := @Normalization.ordinary_hom.{t + 1, t, t + 1, t + 2} T.ProEt inferInstance
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) inferInstance
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
    (WeilConjectures.integralCoefficientAbSheafify.{t, t} T)
    (fun U ↦ reductionModulesHasDerivedCategory T U)
    (fun {U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
      (f : U ⟶ V) ↦ scalarPresentation T f) nrm R S V a b M U x s v
  with_unfolding_all exact hh

private def ordinaryCollapse (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    reductionChange T a ⋙ reductionChange T b ≅ reductionChange T c :=
  by
  subst c
  exact ordinaryAssoc T nrm a b

private theorem ordinaryCollapse_formula (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U)
    (s : S.obj.obj U) (v : V.obj.obj U) :
    ((ordinaryCollapse T nrm a b c h).hom.app M).val.app U
      (reductionTensorSection T b ((reductionChange T a).obj M) U v
        (reductionTensorSection T a M U s x)) =
      reductionTensorSection T c M U (b.hom.app U s * v) x := by
  subst c
  simpa only [ordinaryCollapse, eqToIso_refl, Iso.trans_refl] using
    ordinaryAssoc_formula T nrm a b M U x s v

attribute [local irreducible] ordinaryAssoc ordinaryCollapse reductionBalance

private theorem balance_eq_of_formula (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (e : reductionChange T a ⋙ reductionChange T b ≅ reductionChange T c)
    (he : ∀ (M : reductionModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U)
      (s : S.obj.obj U) (v : V.obj.obj U),
      (e.hom.app M).val.app U
        (reductionTensorSection T b ((reductionChange T a).obj M) U v
          (reductionTensorSection T a M U s x)) =
        reductionTensorSection T c M U (b.hom.app U s * v) x)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P =
      reductionBalance T a b c h P := by
  apply reductionBalance_hom_ext T a b c h P
  intro i U s r x
  exact (he (P.X i) U x r s).trans
    ((congrArg (fun q ↦ reductionTensorSection T c (P.X i) U q x)
      (mul_comm _ _)).trans (reductionBalance_tmul T a b c h P i U s r x).symm)

private theorem collapse_complex_eq (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (Functor.mapHomologicalComplexCompIso
      (ordinaryCollapse T nrm a b c h) (.up ℤ)).hom.app P =
      reductionBalance T a b c h P :=
  balance_eq_of_formula T a b c h (ordinaryCollapse T nrm a b c h)
    (ordinaryCollapse_formula T nrm a b c h) P

/-- The canonical successive scalar normalization of N, using the recorded normalized family. -/
def thetaN (nrm : ScalarNormalization X)
    (b a : ℕ) (h : a ≤ b) :
    N d g b ⋙ reductionDerivedChange X (reductionCoefficientMap X d b a h) ≅ N d g a :=
  Functor.isoWhiskerLeft (PulledReduction.source d g)
    (Eq.ndrec (motive := fun c ↦
      reductionDerivedChange X (OrderedExchange.quotient d X b) ⋙
        reductionDerivedChange X (reductionCoefficientMap X d b a h) ≅
          reductionDerivedChange X c)
      (scalarAssoc X nrm (OrderedExchange.quotient d X b)
        (reductionCoefficientMap X d b a h)) (quotientComp d X b a h))

/-- The coefficient-square equation needed for the canonical inverse scalar mate. -/
def QuotientCompatibility : Prop :=
  ∀ (b a : ℕ) (h : a ≤ b),
    (d.finiteRingIso g b).hom ≫ reductionCoefficientMap X d b a h =
      (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map
        (reductionCoefficientMap Y d b a h) ≫ (d.finiteRingIso g a).hom

private theorem quotientCompatibility : QuotientCompatibility d g := by
  intro b a h
  let j : op b ⟶ op a := (homOfLE h).op
  change (d.finiteRingIso g b).hom ≫ (reductionCoefficientSystem X d).map j =
    (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map
      ((reductionCoefficientSystem Y d).map j) ≫ (d.finiteRingIso g a).hom
  let eU := pbcConstantSystemComparison X d
  let eV := pbcConstantSystemComparison Y d
  let nt : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage g CommRingCat.{t + 1} ⟶
      adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence (fun k ↦ (proEtaleConstantComparison g).app
      (CommRingCat.of (A ⧸ d.ideal ^ (k + 1)))) (by
        intro k
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison g).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (k + 1))))
  have hn := congrArg (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map
    (eV.inv.naturality j)
  have hb := nt.naturality j
  have hu := eU.hom.naturality j
  simp only [Functor.map_comp] at hn
  change (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map
      ((reductionCoefficientSystem Y d).map j) ≫
        (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map
          (pbcLevelConstantComparison Y d a).inv =
    (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map
      (pbcLevelConstantComparison Y d b).inv ≫
        (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map
          ((adicLisseRingSystem Y d.ideal).map j) at hn
  change (adicLisseRingSystem Y d.ideal ⋙
    proEtaleSheafInverseImage g CommRingCat.{t + 1}).map j ≫
      (proEtaleConstantComparison g).app (d.ringTower.obj (op a)) =
    (proEtaleConstantComparison g).app (d.ringTower.obj (op b)) ≫
      (adicLisseRingSystem X d.ideal).map j at hb
  change (adicLisseRingSystem X d.ideal).map j ≫
      (pbcLevelConstantComparison X d a).hom =
    (pbcLevelConstantComparison X d b).hom ≫
      (reductionCoefficientSystem X d).map j at hu
  dsimp only [AdicCoefficientDatum.finiteRingIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [Category.assoc]
  erw [← hu]
  rw [← Category.assoc _ _ ((pbcLevelConstantComparison X d a).hom)]
  rw [← hb]
  simp only [Functor.comp_map, Category.assoc]
  rw [← reassoc_of% hn]

/-- Theta for H is the inverse scalar/pullback mate followed by pullback of the
specified completed normalization; no free comparison morphism is substituted. -/
def thetaH (hq : QuotientCompatibility d g) (b a : ℕ) (h : a ≤ b) :
    H d g b ⋙ reductionDerivedChange X (reductionCoefficientMap X d b a h) ⟶ H d g a :=
  (Functor.associator (d.reduction Y b) (finitePull d g b).mapDerivedCategory
      (reductionDerivedChange X (reductionCoefficientMap X d b a h))).hom ≫
    Functor.whiskerLeft (d.reduction Y b)
      (proEtaleReductionPullbackInv g (d.finiteRing Y b) (d.finiteRing Y a)
        (d.finiteRing X b) (d.finiteRing X a)
        (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
        (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)) ≫
    (Functor.associator (d.reduction Y b)
      (reductionDerivedChange Y (reductionCoefficientMap Y d b a h))
      (finitePull d g a).mapDerivedCategory).inv ≫
    Functor.whiskerRight (completedReductionDerivedNormalization Y d b a h)
      (finitePull d g a).mapDerivedCategory

attribute [local irreducible] thetaH

/-- The specified normalization is an isomorphism of functors. -/
@[instance]
private theorem completedReductionDerivedNormalization_isIso (T : Scheme.{t})
    (b a : ℕ) (h : a ≤ b) :
    IsIso (completedReductionDerivedNormalization T d b a h) :=
  (completedReductionDerivedNormalization_exists T d b a h).choose_spec.1.1

private theorem thetaH_isIso (hq : QuotientCompatibility d g) (b a : ℕ) (h : a ≤ b) :
    IsIso (thetaH d g hq b a h) := by
  have := proEtaleReductionPullbackInv_isIso g (d.finiteRing Y b) (d.finiteRing Y a)
    (d.finiteRing X b) (d.finiteRing X a)
    (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
    (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)
  unfold thetaH
  infer_instance

/-- Ordinary inverse image of a section, with its finite scalar action retained. -/
def finiteGenerator (n : ℕ) (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryH d g n).obj M).val.obj ((proEtaleBaseChange g).op.obj U) :=
  ((proEtaleRingModuleAdjunction g (d.finiteRing Y n) (d.finiteRing X n)
      (d.finiteRingIso g n)).unit.app ((reductionChange Y (d.projection Y n)).obj M)).val.app U
    (reductionTensorSection Y (d.projection Y n) M U 1 x)

/-- The ordinary source of the finite comparison, using the same exact inverse image
as the strict-tower comparison. -/
abbrev ordinaryN (n : ℕ) := PulledReduction.ordinarySource d g ⋙
  reductionChange X (OrderedExchange.quotient d X n)

/-- Inverse-image generator with its target scalar action made explicit. -/
def constantGenerator (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((PulledReduction.ordinarySource d g).obj M).val.obj ((proEtaleBaseChange g).op.obj U) :=
  (((proEtaleRingModuleAdjunction g (exchangeConstantRing Y A)
    (exchangeConstantRing X A) (exchangeConstantIso g A)).unit.app
      ((PulledReduction.res d Y).obj M)).val.app U x)

/-- The comparison from N_n to its common ordinary K-flat computation. -/
def nCounit (n : ℕ) (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    (N d g n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ordinaryN d g n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (reductionDerivedChange X (OrderedExchange.quotient d X n)).map
      ((PulledReduction.ordinarySource d g).mapDerivedCategoryFactors.hom.app P) ≫
    reductionScalarComplexCounit X (OrderedExchange.quotient d X n)
      (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P)

/-- The actual derived scalar associator between two quotient changes. -/
def quotientAssociator
    (nrm : ScalarNormalization X)
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    reductionDerivedChange X (reductionCoefficientMap X d c b hbc) ⋙
        reductionDerivedChange X (reductionCoefficientMap X d b a hab) ≅
      reductionDerivedChange X (reductionCoefficientMap X d c a (hab.trans hbc)) :=
  Eq.ndrec (motive := fun q ↦
    reductionDerivedChange X (reductionCoefficientMap X d c b hbc) ⋙
      reductionDerivedChange X (reductionCoefficientMap X d b a hab) ≅
        reductionDerivedChange X q)
    (scalarAssoc X nrm (reductionCoefficientMap X d c b hbc)
      (reductionCoefficientMap X d b a hab))
    (reductionCoefficientMap_comp X d c b a hab hbc)

/-- All finite normalization data and laws, fixed on actual sheaf tensor complexes.
The ordinary formulas use scalar-first tensors, as does the recorded coefficient datum. -/
structure Comparison where
  /-- Compatibility of the specified finite coefficient identifications. -/
  quotientCompatibility : QuotientCompatibility d g
  /-- The recorded coherent normalization specialized to the actual scalar functors. -/
  scalarNormalization : ScalarNormalization X
  /-- The finite coefficient isomorphisms of the specified strict comparison. -/
  tau : ∀ n : ℕ, N d g n ≅ H d g n
  /-- Its ordinary balanced section map, before derived localization. -/
  ordinaryTau : ∀ n : ℕ, ordinaryN d g n ≅ ordinaryH d g n
  /-- Normalization of tau on inverse-image generators, including target coefficients. -/
  ordinaryTau_formula : ∀ (n : ℕ) (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (r : (exchangeConstantRing X A).obj.obj ((proEtaleBaseChange g).op.obj U))
    (s : (d.finiteRing X n).obj.obj ((proEtaleBaseChange g).op.obj U)),
    ((ordinaryTau n).hom.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (OrderedExchange.quotient d X n)
        ((PulledReduction.ordinarySource d g).obj M) ((proEtaleBaseChange g).op.obj U) s
        (r • constantGenerator d g M U x)) =
      (((OrderedExchange.quotient d X n).hom.app
        ((proEtaleBaseChange g).op.obj U) r) * s) • finiteGenerator d g n M U x
  /-- Both universal counits compute every flat-term K-flat completed representative. -/
  computed : ∀ (n : ℕ) (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ),
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
      (d.completedRing Y) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      Y.ProEt inferInstance (ProEt.topology Y) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} Y)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} Y).isRightAdjoint
      (d.completedRing Y) (P.X i)) →
    IsIso (nCounit d g n P) ∧ IsIso (hCounit d g n P)
  /-- The finite derived map is the localization of this particular ordinary map. -/
  tau_representative :
    ∀ (n : ℕ) (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ),
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
      (d.completedRing Y) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      Y.ProEt inferInstance (ProEt.topology Y) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} Y)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} Y).isRightAdjoint
      (d.completedRing Y) (P.X i)) →
    (tau n).hom.app (DerivedCategory.Q.obj P) ≫ hCounit d g n P =
      nCounit d g n P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinaryTau n) (.up ℤ)).hom.app P)
  /-- Invertibility in the quotient-coefficient category. -/
  thetaH_isIso : ∀ (b a : ℕ) (h : a ≤ b), IsIso (thetaH d g quotientCompatibility b a h)
  /-- The square thetaH (tau_b tensor 1) = tau_a thetaN, naturally in K. -/
  square : ∀ (b a : ℕ) (h : a ≤ b) (K : d.derived Y),
    (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map ((tau b).hom.app K) ≫
        (thetaH d g quotientCompatibility b a h).app K =
      (thetaN d g scalarNormalization b a h).hom.app K ≫ (tau a).hom.app K
  /-- The triple-normalization equality under canonical derived scalar associativity. -/
  associative : ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (K : d.derived Y),
    (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
        ((thetaH d g quotientCompatibility c b hbc).app K) ≫
        (thetaH d g quotientCompatibility b a hab).app K =
      (quotientAssociator d scalarNormalization c b a hab hbc).hom.app ((H d g c).obj K) ≫
        (thetaH d g quotientCompatibility c a (hab.trans hbc)).app K
  /-- Ordinary theta, a natural map of the actual pulled module tensor functors. -/
  ordinaryTheta : ∀ (b a : ℕ) (h : a ≤ b),
    ordinaryH d g b ⋙ reductionChange X (reductionCoefficientMap X d b a h) ≅
      ordinaryH d g a
  /-- Its balancing formula after inverse image and scalar extension. -/
  ordinaryTheta_formula : ∀ (b a : ℕ) (h : a ≤ b)
    (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (s : (d.finiteRing X b).obj.obj ((proEtaleBaseChange g).op.obj U))
    (v : (d.finiteRing X a).obj.obj ((proEtaleBaseChange g).op.obj U)),
    ((ordinaryTheta b a h).hom.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d b a h)
        ((ordinaryH d g b).obj M) ((proEtaleBaseChange g).op.obj U) v
        (s • finiteGenerator d g b M U x)) =
      (((reductionCoefficientMap X d b a h).hom.app ((proEtaleBaseChange g).op.obj U) s) * v) •
        finiteGenerator d g a M U x
  /-- Both triple composites before localization have the same balanced value.
  Naturality of scalar extension and the two ordinary normalization maps give the
  first route; quotient associativity gives the second route. -/
  ordinaryTriple_formula : ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (t : (d.finiteRing X c).obj.obj ((proEtaleBaseChange g).op.obj U))
    (s : (d.finiteRing X b).obj.obj ((proEtaleBaseChange g).op.obj U))
    (v : (d.finiteRing X a).obj.obj ((proEtaleBaseChange g).op.obj U)),
    ((reductionChange X (reductionCoefficientMap X d b a hab)).map
      ((ordinaryTheta c b hbc).hom.app M) ≫ (ordinaryTheta b a hab).hom.app M).val.app
        ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d b a hab)
        ((reductionChange X (reductionCoefficientMap X d c b hbc)).obj
          ((ordinaryH d g c).obj M)) ((proEtaleBaseChange g).op.obj U) v
        (reductionTensorSection X (reductionCoefficientMap X d c b hbc)
          ((ordinaryH d g c).obj M) ((proEtaleBaseChange g).op.obj U) s
          (t • finiteGenerator d g c M U x))) =
      ((((reductionCoefficientMap X d c a (hab.trans hbc)).hom.app
          ((proEtaleBaseChange g).op.obj U) t) *
        ((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s)) * v) • finiteGenerator d g a M U x ∧
    ((ordinaryTheta c a (hab.trans hbc)).hom.app M).val.app
      ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d c a (hab.trans hbc))
        ((ordinaryH d g c).obj M) ((proEtaleBaseChange g).op.obj U)
        (((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s) * v)
        (t • finiteGenerator d g c M U x)) =
      ((((reductionCoefficientMap X d c a (hab.trans hbc)).hom.app
          ((proEtaleBaseChange g).op.obj U) t) *
        ((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s)) * v) • finiteGenerator d g a M U x
  /-- The specified thetaH is precisely the map induced on flat-term K-flat complexes. -/
  theta_representative : ∀ (b a : ℕ) (h : a ≤ b)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ),
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
      (d.completedRing Y) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      Y.ProEt inferInstance (ProEt.topology Y) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} Y)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} Y).isRightAdjoint
      (d.completedRing Y) (P.X i)) →
    (thetaH d g quotientCompatibility b a h).app (DerivedCategory.Q.obj P) ≫
        hCounit d g a P =
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map (hCounit d g b P) ≫
        reductionScalarComplexCounit X (reductionCoefficientMap X d b a h)
          (((ordinaryH d g b).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryTheta b a h) (.up ℤ)).hom.app P)
  /-- Ordinary extension along the equal-index quotient, normalized as multiplication. -/
  ordinaryUnit : ∀ a : ℕ,
    reductionChange X (reductionCoefficientMap X d a a (le_refl a)) ≅
      𝟭 (reductionModules X (d.finiteRing X a))
  /-- The unit identification on every local tensor, not an unspecified automorphism. -/
  ordinaryUnit_formula : ∀ (a : ℕ) (M : reductionModules X (d.finiteRing X a))
    (U : X.ProEtᵒᵖ) (s : (d.finiteRing X a).obj.obj U) (x : M.val.obj U),
    ((ordinaryUnit a).hom.app M).val.app U
      (reductionTensorSection X (reductionCoefficientMap X d a a (le_refl a)) M U s x) =
        s • x
  /-- The unit is its exact derived localization through the universal scalar counit. -/
  derivedUnit : ∀ a : ℕ,
    reductionDerivedChange X (reductionCoefficientMap X d a a (le_refl a)) ≅
      𝟭 (reductionDerivedCategory X (d.finiteRing X a))
  /-- Its representative computation fixes the derived scalar unit uniquely. -/
  unit_representative : ∀ (a : ℕ)
    (P : CochainComplex (reductionModules X (d.finiteRing X a)) ℤ),
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} X.ProEt) (ProEt.topology X)
      (d.finiteRing X a) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} X)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} X).isRightAdjoint
      (d.finiteRing X a) (P.X i)) →
    (derivedUnit a).hom.app (DerivedCategory.Q.obj P) =
      reductionScalarComplexCounit X (reductionCoefficientMap X d a a (le_refl a)) P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryUnit a) (.up ℤ)).hom.app P)
  /-- Equal-index thetaH is the scalar-extension unit identification. -/
  unit : ∀ (a : ℕ) (K : d.derived Y),
    (thetaH d g quotientCompatibility a a (le_refl a)).app K =
      (derivedUnit a).hom.app ((H d g a).obj K)

attribute [local irreducible] HasDerivedCategory.standard

-- Prefer the original site's fixed universe to imported universe-raising instances.
private theorem originalSiteSmall (T : Scheme.{t}) : EssentiallySmall.{t + 1} T.ProEt :=
  essentiallySmallSelf.{0} T.ProEt
attribute [local instance 2000] originalSiteSmall

private theorem completed_flat (T : Scheme.{t}) :
    @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      T.ProEt inferInstance (ProEt.topology T) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} T).isRightAdjoint
      (exchangeConstantRing T A)
      ((reductionRestrict T (exchangeScalar d T)).obj
        (SheafOfModules.unit (reductionModuleRing T (d.completedRing T)))) := by
  have : IsNoetherianRing A := d.noetherian
  apply CompletedConstantAlgebra.flat_presented_completion T d.ideal
    (pbcCompletedComparison T d) (exchangeScalar d T)
  intro n
  dsimp only [exchangeScalar]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n

private theorem pullback_good {U V : Scheme.{t}} (f : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (P : CochainComplex (proEtaleRingModules V R) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      V.ProEt inferInstance (essentiallySmallSelf.{0} V.ProEt) (ProEt.topology V) R P)
    (hflat : ∀ n : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      V.ProEt inferInstance (ProEt.topology V) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} V)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} V).isRightAdjoint R (P.X n)) :
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      U.ProEt inferInstance (essentiallySmallSelf.{0} U.ProEt) (ProEt.topology U) S
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ n : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      U.ProEt inferInstance (ProEt.topology U) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} U)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} U).isRightAdjoint S
      ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P).X n) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists.{t} f R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (t + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 V)).2.2.2.1
  let IM : proEtaleRingModules V R ⥤ proEtaleRingModules U
      ((proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R) :=
    @SheafOfModules.AlgebraicInverseImage.modules.{t + 1, t + 1, t, t + 1, t}
      V.ProEt U.ProEt inferInstance inferInstance (essentiallySmallSelf.{0} V.ProEt)
      (essentiallySmallSelf.{0} U.ProEt) (ProEt.topology V) (ProEt.topology U)
      (proEtaleSheafInverseImage f (Type (t + 1))) R
      ((proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R) I
  let C := proEtaleRingModules V R
  let D := proEtaleRingModules U ((proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R)
  have hobj (N : C) : (proEtaleRingModulePullback f R S c).obj N =
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom
        (IM.obj N) :=
    congrArg (SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom)
      (Functor.congr_obj hI.symm N)
  refine @SheafOfModules.isKFlat_ringedToposPullback.{t + 1, t, t + 1, t, t + 1}
    V.ProEt U.ProEt inferInstance inferInstance (essentiallySmallSelf.{0} V.ProEt)
    (essentiallySmallSelf.{0} U.ProEt) (ProEt.topology V) (ProEt.topology U) R S
    ((proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R)
    (proEtaleSheafInverseImage f (Type (t + 1)))
    (proEtaleSheafDirectImage f (Type (t + 1)))
    (proEtaleSheafAdjunction f (Type (t + 1))) inferInstance I c.hom
    (proEtaleRingModulePullback f R S c) hobj ?_ inferInstance P hP hflat
  intro M N a
  have aux (F G : C ⥤ D) (h : F = G) :
      SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} c.hom (F.obj M) (F.map a) =
        eqToHom (congrArg (fun E : C ⥤ D ↦
          SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom (E.obj M)) h) ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} c.hom (G.obj M) (G.map a) ≫
        eqToHom (congrArg (fun E : C ⥤ D ↦
          SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom (E.obj N)) h).symm := by
    subst G
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact aux (proEtaleModuleInverseImage f R) IM hI.symm

private theorem computed (n : ℕ)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
      (d.completedRing Y) P)
    (hflat : ∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      Y.ProEt inferInstance (ProEt.topology Y) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} Y)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} Y).isRightAdjoint
      (d.completedRing Y) (P.X i)) :
    IsIso (nCounit d g n P) ∧ IsIso (hCounit d g n P) := by
  obtain ⟨hr, hrf⟩ := @SheafOfModules.isKFlat_restrictScalars_of_flat.{t + 1, t, t + 1}
    Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
    (exchangeConstantRing Y A) (d.completedRing Y)
    (exchangeScalar d Y) (completed_flat d Y) P hP
  have hp := OrderedExchange.pullback_kFlat.{t} g (exchangeConstantRing Y A)
    (exchangeConstantRing X A) (exchangeConstantIso g A)
    (((PulledReduction.res d Y).mapHomologicalComplex (.up ℤ)).obj P) hr (hrf hflat)
  have hn := scalarCounit_isIso.{t} X (OrderedExchange.quotient d X n)
    (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P) hp
  have hh := scalarCounit_isIso.{t} Y (d.projection Y n) P hP
  constructor
  · unfold nCounit
    infer_instance
  · unfold hCounit
    infer_instance

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

private theorem canonicalTranspose (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S) :
    ∀ (P : CochainComplex (reductionModules T R) ℤ)
      (K : CochainComplex (reductionModules T S) ℤ)
      (f : ((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    (pbcDerivedScalarAdjunction a).homEquiv _ _
      (reductionScalarComplexCounit T a P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          (((pbcScalarAdjunction a).mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
            (reductionRestrict T a).mapDerivedCategoryFactors.inv.app K := by
  obtain ⟨ad, had⟩ := SheafOfModules.sheafRingDerivedHomComparison.{t + 2, t + 1, t + 1, t} a
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

private theorem scalar_unit_formula (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((@pbcScalarAdjunction.{t} T R S a).unit.app M).val.app U x =
      reductionTensorSection T a M U 1 x := by
  unfold pbcScalarAdjunction
  simpa only [pbcTensorSection, reductionTensorSection] using
    (@pbcScalarAdjunction_exists.{t} T R S a).exists.choose_spec M U x

private def ordinaryIdentity (T : Scheme.{t})
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ R) (ha : a = 𝟙 R) :
    reductionChange T a ≅ 𝟭 (reductionModules T R) :=
  ((pbcScalarAdjunction a).ofNatIsoRight
    (SheafOfModules.systemScalarRestrictionUnit a ha)).leftAdjointUniq Adjunction.id

private theorem ordinaryIdentity_formula (T : Scheme.{t})
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ R) (ha : a = 𝟙 R)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) :
    ((ordinaryIdentity T a ha).hom.app M).val.app U
      (reductionTensorSection T a M U s x) = s • x := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((pbcScalarAdjunction a).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionUnit a ha)) Adjunction.id M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have hx := congrArg (fun f : M ⟶ M ↦ f.val.app U x) h
  change ((pbcScalarAdjunction a).homEquiv M M
    ((ordinaryIdentity T a ha).hom.app M)).val.app U x = x at hx
  rw [Adjunction.homEquiv_unit] at hx
  change ((ordinaryIdentity T a ha).hom.app M).val.app U
    (((pbcScalarAdjunction a).unit.app M).val.app U x) = x at hx
  erw [scalar_unit_formula] at hx
  have hs := tensorSection_smul T a M U s 1 x
  rw [mul_one] at hs
  rw [← hs, map_smul]
  exact congrArg (s • ·) hx

attribute [local irreducible] ordinaryIdentity

private def derivedIdentity (T : Scheme.{t})
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ R) (ha : a = 𝟙 R) :
    reductionDerivedChange T a ≅ 𝟭 (reductionDerivedCategory T R) :=
  ((pbcDerivedScalarAdjunction a).ofNatIsoRight
    (Functor.exactDerivedRestrictionUnit (reductionRestrict T a)
      (SheafOfModules.systemScalarRestrictionUnit a ha))).leftAdjointUniq Adjunction.id

private theorem derivedIdentity_rep (T : Scheme.{t})
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ R) (ha : a = 𝟙 R)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (derivedIdentity T a ha).hom.app (DerivedCategory.Q.obj P) =
      reductionScalarComplexCounit T a P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinaryIdentity T a ha) (.up ℤ)).hom.app P) := by
  let F := reductionRestrict T a
  let η := SheafOfModules.systemScalarRestrictionUnit a ha
  let δ := Functor.exactDerivedRestrictionUnit F η
  let ν := ordinaryIdentity T a ha
  let ac := (pbcScalarAdjunction a).mapHomologicalComplex (.up ℤ)
  let ηc := NatIso.mapHomologicalComplex η (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let νc := NatIso.mapHomologicalComplex ν (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  have hn : ∀ Q, ac.homEquiv _ _ (νc.hom.app Q) ≫ ηc.hom.app Q = 𝟙 Q := by
    intro Q
    apply HomologicalComplex.hom_ext
    intro i
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((pbcScalarAdjunction a).ofNatIsoRight η) Adjunction.id (Q.X i)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
    rw [Adjunction.homEquiv_unit]
    simp only [ac, νc, ηc, Iso.trans_hom, NatTrans.comp_app,
      HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
      Functor.mapHomologicalComplexIdIso_hom_app_f,
      Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.id_f]
    erw [Category.comp_id, Category.comp_id]
    with_unfolding_all exact h
  have h := CategoryTheory.normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
    ac Adjunction.id (pbcDerivedScalarAdjunction a) Adjunction.id
    (reductionScalarComplexCounit T a) (fun _ ↦ 𝟙 _)
    F.mapDerivedCategoryFactors.inv.app (fun _ ↦ 𝟙 _) (canonicalTranspose T a)
    (identityNormalization DerivedCategory.Q)
    ηc δ νc.hom.app hn (by
      intro K
      simpa only [Category.comp_id] using
        Functor.exactDerivedRestrictionUnit_inv_factors F η K) P
  have hv : νc.hom.app P = (NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app P := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [νc, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f,
      Functor.mapHomologicalComplexIdIso_hom_app_f]
    exact Category.comp_id _
  rw [hv, Category.comp_id] at h
  exact h

attribute [local irreducible] derivedIdentity

private theorem quotient_constant (T : Scheme.{t}) (n : ℕ) :
    OrderedExchange.quotient d T n =
      (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
          (pbcLevelConstantComparison T d n).hom := by
  dsimp only [OrderedExchange.quotient, exchangeScalar, AdicCoefficientDatum.projection,
    completedReductionProjection, pbcCompletedComparison]
  rw [Category.assoc]
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc]
  erw [(adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n]
  rfl

private theorem quotient_surjective (T : Scheme.{t}) (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective ((OrderedExchange.quotient d T n).hom.app U) := by
  classical
  have : IsNoetherianRing A := d.noetherian
  let V := op (AsSmall.up.obj U.unop)
  let α := (CompletedConstantAlgebra.constantsIso T).app (CommRingCat.of A)
  let δ := (CompletedConstantAlgebra.pushRing T).mapIso
      (pbcLevelConstantComparison T d n).symm ≪≫
    (CompletedConstantAlgebra.constantsIso T).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
  have heq (r : (exchangeConstantRing T A).obj.obj U) :
      (ConstantCompletion.quotient (CompletedConstantAlgebra.smallTopology T) A d.ideal n).hom.app V
        (α.hom.hom.app V r) =
      δ.hom.hom.app V ((OrderedExchange.quotient d T n).hom.app U r) := by
    have hn := (CompletedConstantAlgebra.constantsIso T).hom.naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))
    have h := congrArg (fun f ↦ f.hom.app V r) hn
    dsimp only [δ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [quotient_constant]
    change _ = ((CompletedConstantAlgebra.constantsIso T).hom.app _).hom.app V
      ((pbcLevelConstantComparison T d n).inv.hom.app U
        ((pbcLevelConstantComparison T d n).hom.hom.app U
          (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
            (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).hom.app U r)))
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app U) (pbcLevelConstantComparison T d n).hom_inv_id)
    change ∀ z, (pbcLevelConstantComparison T d n).inv.hom.app U
      ((pbcLevelConstantComparison T d n).hom.hom.app U z) = z at hi
    rw [hi]
    exact h.symm
  intro s
  obtain ⟨r, hr⟩ :=
    ((ConstantCompletion.flat_and_quotients
      (CompletedConstantAlgebra.smallTopology T) A d.ideal).2.2 n V.unop).1
      (δ.hom.hom.app V s)
  refine ⟨α.inv.hom.app V r, ?_⟩
  have h := heq (α.inv.hom.app V r)
  have hα := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app V) α.inv_hom_id) r
  change α.hom.hom.app V (α.inv.hom.app V r) = r at hα
  rw [hα, hr] at h
  have hδ (z : (d.finiteRing T n).obj.obj U) :
      δ.inv.hom.app V (δ.hom.hom.app V z) = z :=
    ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app V) δ.hom_inv_id) z
  exact (hδ _).symm.trans ((congrArg (δ.inv.hom.app V) h).symm.trans (hδ _))

private def cancelScalarRestriction
    {C D E : Type*} [Category C] [Category D] [Category E]
    (U : D ⥤ E) (ff : U.FullyFaithful) {F G : C ⥤ D}
    (e : F ⋙ U ≅ G ⋙ U) : F ≅ G := by
  refine NatIso.ofComponents (fun M ↦ ff.preimageIso (e.app M)) ?_
  intro M N f
  apply ff.map_injective
  simpa only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.app_hom, Functor.comp_map] using
      e.hom.naturality f

private theorem cancelScalarRestriction_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    (U : D ⥤ E) (ff : U.FullyFaithful) {F G : C ⥤ D}
    (e : F ⋙ U ≅ G ⋙ U) (M : C) :
    U.map ((cancelScalarRestriction U ff e).hom.app M) = e.hom.app M :=
  ff.map_preimage _

attribute [local irreducible] cancelScalarRestriction

private def ordinaryCoefficientComparison (T : Scheme.{t}) (n : ℕ) :
    reductionRestrict T (exchangeScalar d T) ⋙
      reductionChange T (OrderedExchange.quotient d T n) ≅
        reductionChange T (d.projection T n) :=
  cancelScalarRestriction (reductionRestrict T (OrderedExchange.quotient d T n))
    (SheafOfModules.ScalarDescent.fullyFaithful
      ((adicLisseForget T).map (OrderedExchange.quotient d T n))
        (quotient_surjective d T n))
    (F := reductionRestrict T (exchangeScalar d T) ⋙
      reductionChange T (OrderedExchange.quotient d T n))
    (G := reductionChange T (d.projection T n))
    (NatIso.ofComponents (fun M ↦ by
      with_unfolding_all exact ((OrderedExchange.ordinaryRho d T).app M).app (op n))
      (by
        intro M N f
        have h := congrArg (fun z ↦ z.app (op n))
          ((OrderedExchange.ordinaryRho d T).hom.naturality f)
        with_unfolding_all exact h))

attribute [local irreducible] ordinaryCoefficientComparison

private theorem ordinaryCoefficientComparison_formula (T : Scheme.{t}) (n : ℕ)
    (M : reductionModules T (d.completedRing T)) (U : T.ProEtᵒᵖ)
    (s : (d.finiteRing T n).obj.obj U) (x : M.val.obj U) :
    ((ordinaryCoefficientComparison d T n).hom.app M).val.app U
      (reductionTensorSection T (OrderedExchange.quotient d T n)
        ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
      reductionTensorSection T (d.projection T n) M U s x := by
  let q := OrderedExchange.quotient d T n
  let F := reductionRestrict T q
  have hm : F.map ((ordinaryCoefficientComparison d T n).hom.app M) =
      (((OrderedExchange.ordinaryRho d T).hom.app M).app (op n)) := by
    unfold ordinaryCoefficientComparison
    with_unfolding_all exact cancelScalarRestriction_map _ _ _ M
  have hx := congrArg (fun f ↦ f.val.app U
    (reductionTensorSection T q ((reductionRestrict T (exchangeScalar d T)).obj M) U s x)) hm
  have hρ := (OrderedExchange.ordinaryRho_existsUnique d T).exists.choose_spec M n U s x
  have hx' : ((ordinaryCoefficientComparison d T n).hom.app M).val.app U
      (reductionTensorSection T q ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) =
        (((OrderedExchange.ordinaryRho d T).hom.app M).app (op n)).val.app U
          (reductionTensorSection T q
            ((reductionRestrict T (exchangeScalar d T)).obj M) U s x) := by
    with_unfolding_all exact hx
  exact hx'.trans hρ

section OrdinaryMate
variable (RV SV : Sheaf (ProEt.topology Y) CommRingCat.{t + 1})
  (RU SU : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
  (aY : RV ⟶ SV) (aX : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage g CommRingCat.{t + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage g CommRingCat.{t + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aX = (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map aY ≫ cS.hom)

private def ordinaryMate :
    proEtaleRingModulePullback g RV RU cR ⋙ reductionChange X aX ≅
      reductionChange Y aY ⋙ proEtaleRingModulePullback g SV SU cS := by
  let m := (mateEquiv (pbcScalarAdjunction aY) (pbcScalarAdjunction aX)).symm
    (TwoSquare.mk (reductionRestrict Y aY) (proEtaleRingModulePullback g SV SU cS)
      (proEtaleRingModulePullback g RV RU cR) (reductionRestrict X aX)
      (proEtaleRingRestrictionPullbackInv g RV SV RU SU aY aX cR cS comm))
  have : IsIso m := by
    with_unfolding_all
      exact OrderedExchange.scalarPull_isIso g RV SV RU SU aY aX cR cS comm
  exact asIso m

attribute [local irreducible] ordinaryMate

private theorem ordinaryMate_hom :
    (ordinaryMate g RV SV RU SU aY aX cR cS comm).hom =
      ((mateEquiv (pbcScalarAdjunction aY) (pbcScalarAdjunction aX)).symm
        (TwoSquare.mk (reductionRestrict Y aY) (proEtaleRingModulePullback g SV SU cS)
          (proEtaleRingModulePullback g RV RU cR) (reductionRestrict X aX)
          (proEtaleRingRestrictionPullbackInv g RV SV RU SU aY aX cR cS comm))) := by
  unfold ordinaryMate
  rfl

private theorem ordinaryMate_one (M : reductionModules Y RV)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryMate g RV SV RU SU aY aX cR cS comm).hom.app M).val.app
        ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X aX
        ((proEtaleRingModulePullback g RV RU cR).obj M)
        ((proEtaleBaseChange g).op.obj U) 1
        (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x)) =
      ((proEtaleRingModuleAdjunction g SV SU cS).unit.app
        ((reductionChange Y aY).obj M)).val.app U
          (reductionTensorSection Y aY M U 1 x) := by
  let β := proEtaleRingRestrictionPullbackInv g RV SV RU SU aY aX cR cS comm
  let adjY := proEtaleRingExtensionAdjunction aY
  let adjX := proEtaleRingExtensionAdjunction aX
  let P := proEtaleRingModulePullback g RV RU cR
  have h := unit_mateEquiv_symm adjY adjX (TwoSquare.mk _ _ _ _ β) M
  have hx := congrArg (fun f ↦ f.val.app ((proEtaleBaseChange g).op.obj U)
    (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x)) h
  have hn := congrArg (fun f ↦ f.val.app U x)
    ((proEtaleRingModuleAdjunction g RV RU cR).unit.naturality (adjY.unit.app M)).symm
  change ((P.map (adjY.unit.app M)).val.app ((proEtaleBaseChange g).op.obj U)
      (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x)) =
    ((proEtaleRingModuleAdjunction g RV RU cR).unit.app
      ((proEtaleRingRestrictScalars aY).obj ((reductionChange Y aY).obj M))).val.app U
        ((adjY.unit.app M).val.app U x) at hn
  with_unfolding_all
    change (β.app ((reductionChange Y aY).obj M)).val.app
        ((proEtaleBaseChange g).op.obj U)
        ((P.map (adjY.unit.app M)).val.app ((proEtaleBaseChange g).op.obj U)
          (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x)) =
      ((ordinaryMate g RV SV RU SU aY aX cR cS comm).hom.app M).val.app
        ((proEtaleBaseChange g).op.obj U)
        ((adjX.unit.app (P.obj M)).val.app ((proEtaleBaseChange g).op.obj U)
          (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x)) at hx
  rw [hn, OrderedExchange.restrictionPullback_unit] at hx
  dsimp only [adjY, adjX, proEtaleRingExtensionAdjunction] at hx
  have huX := scalar_unit_formula X aX (P.obj M) ((proEtaleBaseChange g).op.obj U)
    (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x)
  have huY := scalar_unit_formula Y aY M U x
  have heX := congrArg (fun z ↦
    ((ordinaryMate g RV SV RU SU aY aX cR cS comm).hom.app M).val.app
      ((proEtaleBaseChange g).op.obj U) z) huX
  have heY := congrArg (fun z ↦
    ((proEtaleRingModuleAdjunction g SV SU cS).unit.app
      ((reductionChange Y aY).obj M)).val.app U z) huY
  exact heX.symm.trans (hx.symm.trans heY)

attribute [local irreducible] reductionChange completedAdicChange
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingExtension
attribute [local irreducible] reductionDerivedChange

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derivedMate_rep
    (P : CochainComplex (reductionModules Y RV) ℤ) :
    (proEtaleReductionPullbackInv g RV SV RU SU aY aX cR cS comm).app
        (DerivedCategory.Q.obj P) ≫
      (proEtaleRingModulePullback g SV SU cS).mapDerivedCategory.map
        (reductionScalarComplexCounit Y aY P) ≫
      (proEtaleRingModulePullback g SV SU cS).mapDerivedCategoryFactors.hom.app
        (((reductionChange Y aY).mapHomologicalComplex (.up ℤ)).obj P) =
    (reductionDerivedChange X aX).map
        ((proEtaleRingModulePullback g RV RU cR).mapDerivedCategoryFactors.hom.app P) ≫
      reductionScalarComplexCounit X aX
        (((proEtaleRingModulePullback g RV RU cR).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (ordinaryMate g RV SV RU SU aY aX cR cS comm) (.up ℤ)).hom.app P) := by
  let β := proEtaleRingRestrictionPullbackInv g RV SV RU SU aY aX cR cS comm
  have : IsIso β :=
    proEtaleRingRestrictionPullbackInv_isIso g RV SV RU SU aY aX cR cS comm
  let βI := asIso β
  let βD := (proEtaleRingRestrictionDerivedPullback g RV SV RU SU
    aY aX cR cS comm).inv
  let G := proEtaleRingModulePullback g RV RU cR
  let H := proEtaleRingModulePullback g SV SU cS
  have hβ : βD = (Functor.mapDerivedCategorySquareIso βI).hom := by
    change (Functor.mapDerivedCategorySquareIso βI.symm).inv = _
    have hi : Functor.mapDerivedCategorySquareIso βI.symm =
        (Functor.mapDerivedCategorySquareIso βI).symm :=
      Iso.ext (Functor.square_symm_hom βI)
    simpa only [Iso.symm_inv] using congrArg (fun e ↦ e.inv) hi
  exact exactMateRepresentative
    (C := reductionModules Y RV) (D := reductionModules Y SV)
    (E := reductionModules X RU) (F := reductionModules X SU)
    (reductionChange Y aY) (reductionRestrict Y aY)
    (reductionChange X aX) (reductionRestrict X aX) G H
    (reductionDerivedChange Y aY) (reductionDerivedChange X aX)
    (pbcScalarAdjunction aY) (pbcScalarAdjunction aX)
    (pbcDerivedScalarAdjunction aY) (pbcDerivedScalarAdjunction aX)
    (complexCounitNat (reductionChange Y aY) (reductionDerivedChange Y aY)
      (reductionDerivedCounit Y aY))
    (complexCounitNat (reductionChange X aX) (reductionDerivedChange X aX)
      (reductionDerivedCounit X aX))
    (reductionScalarComplexCounit Y aY) (reductionScalarComplexCounit X aX)
    (by intro Q; rw [complexCounitNat_app])
    (by intro Q; rw [complexCounitNat_app])
    (canonicalTranspose Y aY) (canonicalTranspose X aX)
    βI βD hβ
    (ordinaryMate g RV SV RU SU aY aX cR cS comm).hom
    (ordinaryMate_hom g RV SV RU SU aY aX cR cS comm)
    (proEtaleReductionPullbackInv g RV SV RU SU aY aX cR cS comm) rfl P

end OrdinaryMate

private theorem pullback_unit_naturality
    {V W : Scheme.{t}} (f : V ⟶ W)
    (R : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    {M N : reductionModules W R} (a : M ⟶ N) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((proEtaleRingModulePullback f R S c).map a).val.app
        ((proEtaleBaseChange f).op.obj U)
        (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app U x) =
      ((proEtaleRingModuleAdjunction f R S c).unit.app N).val.app U
        (a.val.app U x) := by
  have h := congrArg (fun z ↦ z.val.app U x)
    ((proEtaleRingModuleAdjunction f R S c).unit.naturality a).symm
  with_unfolding_all exact h

private def ordinaryTau (n : ℕ) : ordinaryN d g n ≅ ordinaryH d g n :=
  normalizedMateIso (PulledReduction.res d Y) (PulledReduction.pull (A := A) g)
    (finitePull d g n) (reductionChange Y (OrderedExchange.quotient d Y n))
    (reductionChange X (OrderedExchange.quotient d X n))
    (reductionChange Y (d.projection Y n))
    (ordinaryMate g (exchangeConstantRing Y A) (d.finiteRing Y n)
      (exchangeConstantRing X A) (d.finiteRing X n)
      (OrderedExchange.quotient d Y n) (OrderedExchange.quotient d X n)
      (exchangeConstantIso g A) (d.finiteRingIso g n) (OrderedExchange.quotient_comm d g n))
    (ordinaryCoefficientComparison d Y n)

private theorem ordinaryTau_one (n : ℕ) (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryTau d g n).hom.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (OrderedExchange.quotient d X n)
        ((PulledReduction.ordinarySource d g).obj M) ((proEtaleBaseChange g).op.obj U) 1
        (constantGenerator d g M U x)) = finiteGenerator d g n M U x := by
  let e := ordinaryCoefficientComparison d Y n
  have hn := pullback_unit_naturality g (d.finiteRing Y n) (d.finiteRing X n)
    (d.finiteRingIso g n) (e.hom.app M) U
    (reductionTensorSection Y (OrderedExchange.quotient d Y n)
      ((PulledReduction.res d Y).obj M) U 1 x)
  dsimp only [e] at hn
  have hc := ordinaryCoefficientComparison_formula d Y n M U 1 x
  erw [hc] at hn
  simp only [ordinaryTau, normalizedMateIso, NatIso.ofComponents_hom_app,
    Iso.app_hom, Functor.mapIso_hom, Iso.trans_hom]
  have hm := ordinaryMate_one g (exchangeConstantRing Y A) (d.finiteRing Y n)
    (exchangeConstantRing X A) (d.finiteRing X n)
    (OrderedExchange.quotient d Y n) (OrderedExchange.quotient d X n)
    (exchangeConstantIso g A) (d.finiteRingIso g n) (OrderedExchange.quotient_comm d g n)
    ((PulledReduction.res d Y).obj M) U x
  have hh := congrArg
    (fun z ↦ ((finitePull d g n).map (e.hom.app M)).val.app
      ((proEtaleBaseChange g).op.obj U) z) hm
  with_unfolding_all exact hh.trans hn

private theorem ordinaryTau_formula (n : ℕ) (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (r : (exchangeConstantRing X A).obj.obj ((proEtaleBaseChange g).op.obj U))
    (s : (d.finiteRing X n).obj.obj ((proEtaleBaseChange g).op.obj U)) :
    ((ordinaryTau d g n).hom.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (OrderedExchange.quotient d X n)
        ((PulledReduction.ordinarySource d g).obj M) ((proEtaleBaseChange g).op.obj U) s
        (r • constantGenerator d g M U x)) =
      (((OrderedExchange.quotient d X n).hom.app
        ((proEtaleBaseChange g).op.obj U) r) * s) • finiteGenerator d g n M U x := by
  rw [tensor_balance, map_smul, ordinaryTau_one]

attribute [local irreducible] ordinaryTau

private def ordinaryTheta (nrm : ScalarNormalization Y) (hq : QuotientCompatibility d g)
    (b a : ℕ) (h : a ≤ b) :
    ordinaryH d g b ⋙ reductionChange X (reductionCoefficientMap X d b a h) ≅
      ordinaryH d g a :=
  normalizedMateIso (reductionChange Y (d.projection Y b)) (finitePull d g b)
    (finitePull d g a) (reductionChange Y (reductionCoefficientMap Y d b a h))
    (reductionChange X (reductionCoefficientMap X d b a h))
    (reductionChange Y (d.projection Y a))
    (ordinaryMate g (d.finiteRing Y b) (d.finiteRing Y a)
      (d.finiteRing X b) (d.finiteRing X a)
      (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
      (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h))
    (ordinaryCollapse Y nrm (d.projection Y b) (reductionCoefficientMap Y d b a h)
      (d.projection Y a) (completedReductionProjection_comp Y d b a h))

private theorem ordinaryTheta_one (nrm : ScalarNormalization Y)
    (hq : QuotientCompatibility d g) (b a : ℕ) (h : a ≤ b)
    (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryTheta d g nrm hq b a h).hom.app M).val.app
      ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d b a h)
        ((ordinaryH d g b).obj M) ((proEtaleBaseChange g).op.obj U) 1
        (finiteGenerator d g b M U x)) = finiteGenerator d g a M U x := by
  let e := ordinaryCollapse Y nrm (d.projection Y b)
    (reductionCoefficientMap Y d b a h) (d.projection Y a)
    (completedReductionProjection_comp Y d b a h)
  have hn := pullback_unit_naturality g (d.finiteRing Y a) (d.finiteRing X a)
    (d.finiteRingIso g a) (e.hom.app M) U
    (reductionTensorSection Y (reductionCoefficientMap Y d b a h)
      ((reductionChange Y (d.projection Y b)).obj M) U 1
      (reductionTensorSection Y (d.projection Y b) M U 1 x))
  dsimp only [e] at hn
  rw [ordinaryCollapse_formula, map_one, one_mul] at hn
  simp only [ordinaryTheta, normalizedMateIso, NatIso.ofComponents_hom_app,
    Iso.app_hom, Functor.mapIso_hom, Iso.trans_hom]
  have hm := ordinaryMate_one g (d.finiteRing Y b) (d.finiteRing Y a)
    (d.finiteRing X b) (d.finiteRing X a)
    (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
    (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)
    ((reductionChange Y (d.projection Y b)).obj M) U
    (reductionTensorSection Y (d.projection Y b) M U 1 x)
  have hh := congrArg
    (fun z ↦ ((finitePull d g a).map (e.hom.app M)).val.app
      ((proEtaleBaseChange g).op.obj U) z) hm
  with_unfolding_all exact hh.trans hn

private theorem ordinaryTheta_formula (nrm : ScalarNormalization Y)
    (hq : QuotientCompatibility d g) (b a : ℕ) (h : a ≤ b)
    (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (s : (d.finiteRing X b).obj.obj ((proEtaleBaseChange g).op.obj U))
    (v : (d.finiteRing X a).obj.obj ((proEtaleBaseChange g).op.obj U)) :
    ((ordinaryTheta d g nrm hq b a h).hom.app M).val.app
      ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d b a h)
        ((ordinaryH d g b).obj M) ((proEtaleBaseChange g).op.obj U) v
        (s • finiteGenerator d g b M U x)) =
      (((reductionCoefficientMap X d b a h).hom.app
        ((proEtaleBaseChange g).op.obj U) s) * v) • finiteGenerator d g a M U x := by
  rw [tensor_balance, map_smul, ordinaryTheta_one]

attribute [local irreducible] ordinaryTheta

section
attribute [local irreducible] reductionChange completedAdicChange
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingExtension
attribute [local irreducible] reductionDerivedChange
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance_reducible] reductionChangeComplex QuotientCompatibility

attribute [local irreducible] proEtaleReductionPullbackInv

private theorem thetaH_hom_app (hq : QuotientCompatibility d g)
    (b a : ℕ) (h : a ≤ b) (K : d.derived Y) :
    (thetaH d g hq b a h).app K =
      (proEtaleReductionPullbackInv g (d.finiteRing Y b) (d.finiteRing Y a)
        (d.finiteRing X b) (d.finiteRing X a)
        (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
        (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)).app
          ((d.reduction Y b).obj K) ≫
      (finitePull d g a).mapDerivedCategory.map
        ((completedReductionDerivedNormalization Y d b a h).app K) := by
  unfold thetaH
  exact normalizedMate_app
    (B := reductionDerivedCategory Y (d.completedRing Y))
    (C := reductionDerivedCategory Y (d.finiteRing Y b))
    (D := reductionDerivedCategory X (d.finiteRing X b))
    (E := reductionDerivedCategory Y (d.finiteRing Y a))
    (F := reductionDerivedCategory X (d.finiteRing X a))
    (d.reduction Y b) (finitePull d g b).mapDerivedCategory
    (finitePull d g a).mapDerivedCategory
    (reductionDerivedChange Y (reductionCoefficientMap Y d b a h))
    (reductionDerivedChange X (reductionCoefficientMap X d b a h)) (d.reduction Y a)
    (proEtaleReductionPullbackInv g (d.finiteRing Y b) (d.finiteRing Y a)
      (d.finiteRing X b) (d.finiteRing X a)
      (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
      (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h))
    (completedReductionDerivedNormalization Y d b a h) K

private theorem ordinaryTheta_complex (nrmY : ScalarNormalization Y)
    (hq : QuotientCompatibility d g) (b a : ℕ) (h : a ≤ b)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ)
    (θ : ordinaryH d g b ⋙ reductionChange X (reductionCoefficientMap X d b a h) ≅
      ordinaryH d g a) (hθ : θ = ordinaryTheta d g nrmY hq b a h) :
    (NatIso.mapHomologicalComplex
      (ordinaryMate g (d.finiteRing Y b) (d.finiteRing Y a)
        (d.finiteRing X b) (d.finiteRing X a)
        (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
        (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)) (.up ℤ)).hom.app
      (((reductionChange Y (d.projection Y b)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((finitePull d g a).mapHomologicalComplex (.up ℤ)).map
        (reductionBalance Y (d.projection Y b) (reductionCoefficientMap Y d b a h)
          (d.projection Y a) (completedReductionProjection_comp Y d b a h) P) =
      (NatIso.mapHomologicalComplex θ (.up ℤ)).hom.app P := by
  unfold QuotientCompatibility at hq
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplex_map_f]
  have hb := congrArg (fun k ↦ k.f i)
    (collapse_complex_eq Y nrmY (d.projection Y b) (reductionCoefficientMap Y d b a h)
      (d.projection Y a) (completedReductionProjection_comp Y d b a h) P)
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f] at hb
  rw [← hb, hθ]
  unfold ordinaryTheta normalizedMateIso
  rfl

private theorem theta_representative (nrmY : ScalarNormalization Y)
    (hq : QuotientCompatibility d g) (b a : ℕ) (h : a ≤ b)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
      (d.completedRing Y) P)
    (θ : ordinaryH d g b ⋙ reductionChange X (reductionCoefficientMap X d b a h) ≅
      ordinaryH d g a) (hθ : θ = ordinaryTheta d g nrmY hq b a h) :
    (thetaH d g hq b a h).app (DerivedCategory.Q.obj P) ≫ hCounit d g a P =
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map (hCounit d g b P) ≫
        reductionScalarComplexCounit X (reductionCoefficientMap X d b a h)
          (((ordinaryH d g b).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          θ (.up ℤ)).hom.app P) := by
  unfold QuotientCompatibility at hq
  let qY := reductionCoefficientMap Y d b a h
  let qX := reductionCoefficientMap X d b a h
  let Fb := finitePull d g b
  let Fa := finitePull d g a
  let Eb := reductionChange Y (d.projection Y b)
  let Ea := reductionChange Y (d.projection Y a)
  let μ := proEtaleReductionPullbackInv g (d.finiteRing Y b) (d.finiteRing Y a)
    (d.finiteRing X b) (d.finiteRing X a) qY qX
    (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)
  let εb := reductionScalarComplexCounit Y (d.projection Y b) P
  let εa := reductionScalarComplexCounit Y (d.projection Y a) P
  let Q := (Eb.mapHomologicalComplex (.up ℤ)).obj P
  let balance := reductionBalance Y (d.projection Y b) qY (d.projection Y a)
    (completedReductionProjection_comp Y d b a h) P
  have hn : (completedReductionDerivedNormalization Y d b a h).app
      (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit Y (d.projection Y a) P =
        (reductionDerivedChange Y qY).map εb ≫
          reductionScalarComplexCounit Y qY Q ≫ DerivedCategory.Q.map balance :=
    (completedReductionDerivedNormalization_exists Y d b a h).choose_spec.1.2 P hP
  have hm := derivedMate_rep g (d.finiteRing Y b) (d.finiteRing Y a)
    (d.finiteRing X b) (d.finiteRing X a) qY qX
    (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h) Q
  have hco := ordinaryTheta_complex d g nrmY hq b a h P θ hθ
  have hmap := map_comp_of_eq DerivedCategory.Q
    ((NatIso.mapHomologicalComplex
      (ordinaryMate g (d.finiteRing Y b) (d.finiteRing Y a)
        (d.finiteRing X b) (d.finiteRing X a) qY qX
        (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)) (.up ℤ)).hom.app Q)
    ((Fa.mapHomologicalComplex (.up ℤ)).map balance)
    ((NatIso.mapHomologicalComplex θ (.up ℤ)).hom.app P) hco
  exact mateRepresentativeComposition
    (C := reductionDerivedCategory Y (d.finiteRing Y b))
    (D := reductionDerivedCategory X (d.finiteRing X b))
    (E := reductionDerivedCategory Y (d.finiteRing Y a))
    (F := reductionDerivedCategory X (d.finiteRing X a))
    (x := (d.reduction Y b).obj (DerivedCategory.Q.obj P))
    (y := DerivedCategory.Q.obj Q)
    (z := (d.reduction Y a).obj (DerivedCategory.Q.obj P))
    (v := DerivedCategory.Q.obj
      (((reductionChange Y qY).mapHomologicalComplex (.up ℤ)).obj Q))
    (w := DerivedCategory.Q.obj ((Ea.mapHomologicalComplex (.up ℤ)).obj P))
    (u := DerivedCategory.Q.obj ((Fb.mapHomologicalComplex (.up ℤ)).obj Q))
    (v' := DerivedCategory.Q.obj ((Fa.mapHomologicalComplex (.up ℤ)).obj
      (((reductionChange Y qY).mapHomologicalComplex (.up ℤ)).obj Q)))
    (w' := DerivedCategory.Q.obj ((Fa.mapHomologicalComplex (.up ℤ)).obj
      ((Ea.mapHomologicalComplex (.up ℤ)).obj P)))
    (u' := DerivedCategory.Q.obj
      (((reductionChange X qX).mapHomologicalComplex (.up ℤ)).obj
        ((Fb.mapHomologicalComplex (.up ℤ)).obj Q)))
    Fb.mapDerivedCategory Fa.mapDerivedCategory
    (reductionDerivedChange Y qY) (reductionDerivedChange X qX) μ εb
    ((completedReductionDerivedNormalization Y d b a h).app (DerivedCategory.Q.obj P))
    εa (reductionScalarComplexCounit Y qY Q) (DerivedCategory.Q.map balance)
    (Fb.mapDerivedCategoryFactors.hom.app Q)
    (Fa.mapDerivedCategoryFactors.hom.app ((Ea.mapHomologicalComplex (.up ℤ)).obj P))
    (Fa.mapDerivedCategoryFactors.hom.app
      (((reductionChange Y qY).mapHomologicalComplex (.up ℤ)).obj Q))
    (reductionScalarComplexCounit X qX ((Fb.mapHomologicalComplex (.up ℤ)).obj Q))
    (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (ordinaryMate g (d.finiteRing Y b) (d.finiteRing Y a)
        (d.finiteRing X b) (d.finiteRing X a) qY qX
        (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)) (.up ℤ)).hom.app Q))
    (DerivedCategory.Q.map ((Fa.mapHomologicalComplex (.up ℤ)).map balance))
    (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex θ (.up ℤ)).hom.app P))
    hn (Fa.mapDerivedCategoryFactors.hom.naturality balance) hm hmap
    ((thetaH d g hq b a h).app (DerivedCategory.Q.obj P))
    (hCounit d g a P) (hCounit d g b P)
    (thetaH_hom_app d g hq b a h (DerivedCategory.Q.obj P))
    rfl rfl

end

private theorem ordinaryTriple_formula (nrm : ScalarNormalization Y)
    (hq : QuotientCompatibility d g) : ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (t : (d.finiteRing X c).obj.obj ((proEtaleBaseChange g).op.obj U))
    (s : (d.finiteRing X b).obj.obj ((proEtaleBaseChange g).op.obj U))
    (v : (d.finiteRing X a).obj.obj ((proEtaleBaseChange g).op.obj U)),
    ((reductionChange X (reductionCoefficientMap X d b a hab)).map
      ((ordinaryTheta d g nrm hq c b hbc).hom.app M) ≫
        (ordinaryTheta d g nrm hq b a hab).hom.app M).val.app
        ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d b a hab)
        ((reductionChange X (reductionCoefficientMap X d c b hbc)).obj
          ((ordinaryH d g c).obj M)) ((proEtaleBaseChange g).op.obj U) v
        (reductionTensorSection X (reductionCoefficientMap X d c b hbc)
          ((ordinaryH d g c).obj M) ((proEtaleBaseChange g).op.obj U) s
          (t • finiteGenerator d g c M U x))) =
      ((((reductionCoefficientMap X d c a (hab.trans hbc)).hom.app
          ((proEtaleBaseChange g).op.obj U) t) *
        ((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s)) * v) • finiteGenerator d g a M U x ∧
    ((ordinaryTheta d g nrm hq c a (hab.trans hbc)).hom.app M).val.app
      ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d c a (hab.trans hbc))
        ((ordinaryH d g c).obj M) ((proEtaleBaseChange g).op.obj U)
        (((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s) * v)
        (t • finiteGenerator d g c M U x)) =
      ((((reductionCoefficientMap X d c a (hab.trans hbc)).hom.app
          ((proEtaleBaseChange g).op.obj U) t) *
        ((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s)) * v) • finiteGenerator d g a M U x := by
  intro c b a hab hbc M U x t s v
  let W := (proEtaleBaseChange g).op.obj U
  let qba := reductionCoefficientMap X d b a hab
  let qcb := reductionCoefficientMap X d c b hbc
  let qca := reductionCoefficientMap X d c a (hab.trans hbc)
  let θcb := (ordinaryTheta d g nrm hq c b hbc).hom.app M
  let θba := (ordinaryTheta d g nrm hq b a hab).hom.app M
  have hcomp (z : (d.finiteRing X c).obj.obj W) :
      qba.hom.app W (qcb.hom.app W z) = qca.hom.app W z := by
    exact congrArg (fun f ↦ f.hom.app W z)
      (reductionCoefficientMap_comp X d c b a hab hbc)
  constructor
  · have he := reductionTensor_map X qba θcb W v
      (reductionTensorSection X qcb ((ordinaryH d g c).obj M) W s
        (t • finiteGenerator d g c M U x))
    have he' := congrArg (fun z ↦ θba.val.app W z) he
    have hf := ordinaryTheta_formula d g nrm hq c b hbc M U x t s
    have hf' := congrArg (fun z : ((ordinaryH d g b).obj M).val.obj W ↦
      θba.val.app W (reductionTensorSection X qba ((ordinaryH d g b).obj M) W v z)) hf
    have hg := ordinaryTheta_formula d g nrm hq b a hab M U x
      (qcb.hom.app W t * s) v
    have hr : (qba.hom.app W (qcb.hom.app W t * s)) * v =
        (qca.hom.app W t * qba.hom.app W s) * v := by
      rw [map_mul, hcomp]
    exact he'.trans (hf'.trans (hg.trans
      (congrArg (fun z ↦ z • finiteGenerator d g a M U x) hr)))
  · exact (ordinaryTheta_formula d g nrm hq c a (hab.trans hbc) M U x t
      (qba.hom.app W s * v)).trans
        (congrArg (fun z ↦ z • finiteGenerator d g a M U x) (mul_assoc _ _ _).symm)

private theorem twoScalarPull_ext
    (RV : Sheaf (ProEt.topology Y) CommRingCat.{t + 1})
    (RU S V : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (cR : (proEtaleSheafInverseImage g CommRingCat.{t + 1}).obj RV ≅ RU)
    (a : RU ⟶ S) (b : S ⟶ V) (M : reductionModules Y RV) (L : reductionModules X V)
    (f h : (reductionChange X b).obj ((reductionChange X a).obj
      ((proEtaleRingModulePullback g RV RU cR).obj M)) ⟶ L)
    (hf : ∀ (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app ((proEtaleBaseChange g).op.obj U)
        (reductionTensorSection X b
          ((reductionChange X a).obj ((proEtaleRingModulePullback g RV RU cR).obj M))
          ((proEtaleBaseChange g).op.obj U) 1
          (reductionTensorSection X a ((proEtaleRingModulePullback g RV RU cR).obj M)
            ((proEtaleBaseChange g).op.obj U) 1
            (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x))) =
      h.val.app ((proEtaleBaseChange g).op.obj U)
        (reductionTensorSection X b
          ((reductionChange X a).obj ((proEtaleRingModulePullback g RV RU cR).obj M))
          ((proEtaleBaseChange g).op.obj U) 1
          (reductionTensorSection X a ((proEtaleRingModulePullback g RV RU cR).obj M)
            ((proEtaleBaseChange g).op.obj U) 1
            (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x)))) : f = h := by
  let PM := (proEtaleRingModulePullback g RV RU cR).obj M
  let AM := (reductionChange X a).obj PM
  apply ((@pbcScalarAdjunction.{t} X S V b).homEquiv AM L).injective
  apply ((@pbcScalarAdjunction.{t} X RU S a).homEquiv
    PM ((reductionRestrict X b).obj L)).injective
  apply ((proEtaleRingModuleAdjunction g RV RU cR).homEquiv M
    ((reductionRestrict X a).obj ((reductionRestrict X b).obj L))).injective
  ext U x
  simp only [Adjunction.homEquiv_unit]
  change f.val.app ((proEtaleBaseChange g).op.obj U)
      (((@pbcScalarAdjunction.{t} X S V b).unit.app AM).val.app
        ((proEtaleBaseChange g).op.obj U)
        (((@pbcScalarAdjunction.{t} X RU S a).unit.app PM).val.app
          ((proEtaleBaseChange g).op.obj U)
          (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x))) =
    h.val.app ((proEtaleBaseChange g).op.obj U)
      (((@pbcScalarAdjunction.{t} X S V b).unit.app AM).val.app
        ((proEtaleBaseChange g).op.obj U)
        (((@pbcScalarAdjunction.{t} X RU S a).unit.app PM).val.app
          ((proEtaleBaseChange g).op.obj U)
          (((proEtaleRingModuleAdjunction g RV RU cR).unit.app M).val.app U x)))
  simpa only [scalar_unit_formula] using hf U x

private theorem pullScalar_ext
    (RV SV : Sheaf (ProEt.topology Y) CommRingCat.{t + 1})
    (SU VU : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (cS : (proEtaleSheafInverseImage g CommRingCat.{t + 1}).obj SV ≅ SU)
    (aY : RV ⟶ SV) (aX : SU ⟶ VU)
    (M : reductionModules Y RV) (L : reductionModules X VU)
    (f h : (reductionChange X aX).obj ((proEtaleRingModulePullback g SV SU cS).obj
      ((reductionChange Y aY).obj M)) ⟶ L)
    (hf : ∀ (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app ((proEtaleBaseChange g).op.obj U)
        (reductionTensorSection X aX
          ((proEtaleRingModulePullback g SV SU cS).obj ((reductionChange Y aY).obj M))
          ((proEtaleBaseChange g).op.obj U) 1
          (((proEtaleRingModuleAdjunction g SV SU cS).unit.app
            ((reductionChange Y aY).obj M)).val.app U
              (reductionTensorSection Y aY M U 1 x))) =
      h.val.app ((proEtaleBaseChange g).op.obj U)
        (reductionTensorSection X aX
          ((proEtaleRingModulePullback g SV SU cS).obj ((reductionChange Y aY).obj M))
          ((proEtaleBaseChange g).op.obj U) 1
          (((proEtaleRingModuleAdjunction g SV SU cS).unit.app
            ((reductionChange Y aY).obj M)).val.app U
              (reductionTensorSection Y aY M U 1 x)))) : f = h := by
  apply ((@pbcScalarAdjunction.{t} X SU VU aX).homEquiv
    ((proEtaleRingModulePullback g SV SU cS).obj ((reductionChange Y aY).obj M)) L).injective
  apply ((proEtaleRingModuleAdjunction g SV SU cS).homEquiv
    ((reductionChange Y aY).obj M) ((reductionRestrict X aX).obj L)).injective
  apply ((@pbcScalarAdjunction.{t} Y RV SV aY).homEquiv M _).injective
  ext U x
  simp only [Adjunction.homEquiv_unit]
  change f.val.app ((proEtaleBaseChange g).op.obj U)
      (((@pbcScalarAdjunction.{t} X SU VU aX).unit.app
          ((proEtaleRingModulePullback g SV SU cS).obj ((reductionChange Y aY).obj M))).val.app
        ((proEtaleBaseChange g).op.obj U)
        (((proEtaleRingModuleAdjunction g SV SU cS).unit.app
          ((reductionChange Y aY).obj M)).val.app U
          (((@pbcScalarAdjunction.{t} Y RV SV aY).unit.app M).val.app U x))) =
    h.val.app ((proEtaleBaseChange g).op.obj U)
      (((@pbcScalarAdjunction.{t} X SU VU aX).unit.app
          ((proEtaleRingModulePullback g SV SU cS).obj ((reductionChange Y aY).obj M))).val.app
        ((proEtaleBaseChange g).op.obj U)
        (((proEtaleRingModuleAdjunction g SV SU cS).unit.app
          ((reductionChange Y aY).obj M)).val.app U
          (((@pbcScalarAdjunction.{t} Y RV SV aY).unit.app M).val.app U x)))
  simpa only [scalar_unit_formula] using hf U x

private theorem ordinaryTheta_unit (nrmY : ScalarNormalization Y)
    (hq : QuotientCompatibility d g) (a : ℕ)
    (M : reductionModules Y (d.completedRing Y)) :
    (ordinaryTheta d g nrmY hq a a (le_refl a)).hom.app M =
      (ordinaryIdentity X (R := d.finiteRing X a)
        (reductionCoefficientMap X d a a (le_refl a))
        (reductionCoefficientMap_id X d a)).hom.app ((ordinaryH d g a).obj M) := by
  unfold QuotientCompatibility at hq
  apply pullScalar_ext g (d.completedRing Y) (d.finiteRing Y a)
    (d.finiteRing X a) (d.finiteRing X a) (d.finiteRingIso g a)
    (d.projection Y a) (reductionCoefficientMap X d a a (le_refl a)) M
    ((ordinaryH d g a).obj M)
  intro U x
  have ht := ordinaryTheta_one d g nrmY hq a a (le_refl a) M U x
  have hi := ordinaryIdentity_formula X
    (reductionCoefficientMap X d a a (le_refl a)) (reductionCoefficientMap_id X d a)
    ((ordinaryH d g a).obj M) ((proEtaleBaseChange g).op.obj U) 1
    (finiteGenerator d g a M U x)
  rw [one_smul] at hi
  exact ht.trans hi.symm

private theorem ordinarySquare (nrm : ScalarNormalization X) (nrmY : ScalarNormalization Y)
    (hq : QuotientCompatibility d g) (b a : ℕ) (h : a ≤ b)
    (M : reductionModules Y (d.completedRing Y)) :
    (reductionChange X (reductionCoefficientMap X d b a h)).map
        ((ordinaryTau d g b).hom.app M) ≫
      (ordinaryTheta d g nrmY hq b a h).hom.app M =
    (ordinaryCollapse X nrm (OrderedExchange.quotient d X b)
      (reductionCoefficientMap X d b a h) (OrderedExchange.quotient d X a)
        (quotientComp d X b a h)).hom.app ((PulledReduction.ordinarySource d g).obj M) ≫
      (ordinaryTau d g a).hom.app M := by
  unfold QuotientCompatibility at hq
  apply twoScalarPull_ext g (exchangeConstantRing Y A) (exchangeConstantRing X A)
    (d.finiteRing X b) (d.finiteRing X a) (exchangeConstantIso g A)
    (OrderedExchange.quotient d X b) (reductionCoefficientMap X d b a h)
    ((PulledReduction.res d Y).obj M) ((ordinaryH d g a).obj M)
  intro U x
  change ((ordinaryTheta d g nrmY hq b a h).hom.app M).val.app _
    (((reductionChange X (reductionCoefficientMap X d b a h)).map
      ((ordinaryTau d g b).hom.app M)).val.app _ _) =
    ((ordinaryTau d g a).hom.app M).val.app _
      (((ordinaryCollapse X nrm _ _ _ _).hom.app _).val.app _ _)
  erw [reductionTensor_map, ordinaryTau_one, ordinaryTheta_one,
    ordinaryCollapse_formula, map_one, one_mul, ordinaryTau_one]

private def good (T : Scheme.{t}) (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    ObjectProperty (CochainComplex (reductionModules T R) ℤ) := fun P ↦
  @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      T.ProEt inferInstance (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) R P ∧
    ∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      T.ProEt inferInstance (ProEt.topology T) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} T).isRightAdjoint R (P.X i)

section
attribute [local irreducible] reductionChange completedAdicChange
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingExtension
attribute [local irreducible] reductionDerivedChange
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private def derivedCollapse (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅ reductionDerivedChange T c :=
  Eq.ndrec (motive := fun z ↦
    reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅ reductionDerivedChange T z)
    (scalarAssoc T nrm a b) h

private theorem derivedCollapse_eq (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    derivedCollapse T nrm a b c h =
      scalarAssoc T nrm a b ≪≫ eqToIso (congrArg (reductionDerivedChange T) h) :=
  transportedIso_eq (reductionDerivedChange T) _ (scalarAssoc T nrm a b) h

private theorem scalarCollapse_rep (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (P : CochainComplex (reductionModules T R) ℤ) (hP : good T R P) :
    (derivedCollapse T nrm a b c h).hom.app
        (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit T c P =
      (reductionDerivedChange T b).map (reductionScalarComplexCounit T a P) ≫
        reductionScalarComplexCounit T b
          (((reductionChange T a).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryCollapse T nrm a b c h) (.up ℤ)).hom.app P) := by
  subst c
  with_unfolding_all
    have hh := @Normalization.representative.{t + 1, t, t + 1, t + 2} T.ProEt inferInstance
      (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} T)
      (fun W ↦ reductionModulesHasDerivedCategory T W)
      (fun {W Z : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
        (f : W ⟶ Z) ↦ scalarPresentation T f) nrm R S V a b P hP.1 hP.2
    simp only [derivedCollapse, ordinaryCollapse]
    dsimp only [reductionScalarComplexCounit]
    erw [counit_eq, counit_eq, counit_eq]
    exact hh

-- These iso equalities certify that the two public data repairs preserve their values.
private theorem thetaN_hom_app (nrm : ScalarNormalization X)
    (b a : ℕ) (h : a ≤ b) (K : d.derived Y) :
    (thetaN d g nrm b a h).hom.app K =
      (derivedCollapse X nrm (OrderedExchange.quotient d X b)
        (reductionCoefficientMap X d b a h) (OrderedExchange.quotient d X a)
        (quotientComp d X b a h)).hom.app ((PulledReduction.source d g).obj K) := by
  exact whiskeredIso_app (PulledReduction.source d g) _ K

private theorem quotientAssociator_hom_app (nrm : ScalarNormalization X)
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (K : reductionDerivedCategory X (d.finiteRing X c)) :
    (quotientAssociator d nrm c b a hab hbc).hom.app K =
      (derivedCollapse X nrm (reductionCoefficientMap X d c b hbc)
        (reductionCoefficientMap X d b a hab)
        (reductionCoefficientMap X d c a (hab.trans hbc))
        (reductionCoefficientMap_comp X d c b a hab hbc)).hom.app K := rfl

-- Quotient compatibility is a theorem, not definitional reduction of the limit projections.
attribute [local irreducible] OrderedExchange.quotient reductionCoefficientMap derivedCollapse

private theorem source_scalar_representative (nrm : ScalarNormalization X)
    (b a : ℕ) (h : a ≤ b)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ)
    (hP : good Y (d.completedRing Y) P) :
    @Eq ((reductionDerivedChange X (reductionCoefficientMap X d b a h)).obj
      ((reductionDerivedChange X (OrderedExchange.quotient d X b)).obj
        (DerivedCategory.Q.obj
          (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P))) ⟶
      DerivedCategory.Q.obj (((ordinaryN d g a).mapHomologicalComplex (.up ℤ)).obj P))
    ((derivedCollapse X nrm (OrderedExchange.quotient d X b)
      (reductionCoefficientMap X d b a h) (OrderedExchange.quotient d X a)
      (quotientComp d X b a h)).hom.app
      (DerivedCategory.Q.obj
        (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      reductionScalarComplexCounit X (OrderedExchange.quotient d X a)
        (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P))
    ((reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
      (reductionScalarComplexCounit X (OrderedExchange.quotient d X b)
        (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      reductionScalarComplexCounit X (reductionCoefficientMap X d b a h)
        (((ordinaryN d g b).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (ordinaryCollapse X nrm (OrderedExchange.quotient d X b)
          (reductionCoefficientMap X d b a h) (OrderedExchange.quotient d X a)
          (quotientComp d X b a h)) (.up ℤ)).hom.app
        (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P))) := by
  obtain ⟨hr, hrf⟩ := @SheafOfModules.isKFlat_restrictScalars_of_flat.{t + 1, t, t + 1}
    Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
    (exchangeConstantRing Y A) (d.completedRing Y)
    (exchangeScalar d Y) (completed_flat d Y) P hP.1
  have hg := pullback_good g (exchangeConstantRing Y A) (exchangeConstantRing X A)
    (exchangeConstantIso g A)
    (((PulledReduction.res d Y).mapHomologicalComplex (.up ℤ)).obj P) hr (hrf hP.2)
  exact scalarCollapse_rep X nrm (OrderedExchange.quotient d X b)
    (reductionCoefficientMap X d b a h) (OrderedExchange.quotient d X a)
    (quotientComp d X b a h)
    (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P) hg

private theorem thetaN_representative (nrm : ScalarNormalization X)
    (b a : ℕ) (h : a ≤ b)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ)
    (hP : good Y (d.completedRing Y) P)
    (δ : reductionChange X (OrderedExchange.quotient d X b) ⋙
      reductionChange X (reductionCoefficientMap X d b a h) ≅
        reductionChange X (OrderedExchange.quotient d X a))
    (hδ : δ = ordinaryCollapse X nrm (OrderedExchange.quotient d X b)
      (reductionCoefficientMap X d b a h) (OrderedExchange.quotient d X a)
      (quotientComp d X b a h)) :
    (thetaN d g nrm b a h).hom.app (DerivedCategory.Q.obj P) ≫ nCounit d g a P =
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map (nCounit d g b P) ≫
        reductionScalarComplexCounit X (reductionCoefficientMap X d b a h)
          (((ordinaryN d g b).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          δ (.up ℤ)).hom.app
                (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let e := derivedCollapse X nrm (OrderedExchange.quotient d X b)
    (reductionCoefficientMap X d b a h) (OrderedExchange.quotient d X a)
    (quotientComp d X b a h)
  have hh := source_scalar_representative d g nrm b a h P hP
  rw [← hδ] at hh
  exact compositorRepresentative
    (C := reductionDerivedCategory X (exchangeConstantRing X A))
    (D := reductionDerivedCategory X (d.finiteRing X b))
    (E := reductionDerivedCategory X (d.finiteRing X a))
    (x := (PulledReduction.source d g).obj (DerivedCategory.Q.obj P))
    (y := DerivedCategory.Q.obj
      (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P))
    (u := DerivedCategory.Q.obj (((ordinaryN d g b).mapHomologicalComplex (.up ℤ)).obj P))
    (v := DerivedCategory.Q.obj
      (((reductionChange X (reductionCoefficientMap X d b a h)).mapHomologicalComplex
        (.up ℤ)).obj (((ordinaryN d g b).mapHomologicalComplex (.up ℤ)).obj P)))
    (w := DerivedCategory.Q.obj (((ordinaryN d g a).mapHomologicalComplex (.up ℤ)).obj P))
    (reductionDerivedChange X (OrderedExchange.quotient d X b))
    (reductionDerivedChange X (reductionCoefficientMap X d b a h))
    (reductionDerivedChange X (OrderedExchange.quotient d X a)) e.hom
    ((PulledReduction.ordinarySource d g).mapDerivedCategoryFactors.hom.app P)
    (reductionScalarComplexCounit X (OrderedExchange.quotient d X b)
      (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P))
    (reductionScalarComplexCounit X (reductionCoefficientMap X d b a h)
      (((ordinaryN d g b).mapHomologicalComplex (.up ℤ)).obj P))
    (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex δ (.up ℤ)).hom.app
      (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P)))
    (reductionScalarComplexCounit X (OrderedExchange.quotient d X a)
      (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P))
    hh ((thetaN d g nrm b a h).hom.app (DerivedCategory.Q.obj P))
    (nCounit d g a P) (nCounit d g b P)
    (thetaN_hom_app d g nrm b a h (DerivedCategory.Q.obj P)) rfl rfl

private theorem scalarCollapse_assoc (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V W : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : V ⟶ W)
    (ab : R ⟶ V) (bc : S ⟶ W) (abc : R ⟶ W)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) (K : reductionDerivedCategory T R) :
    (reductionDerivedChange T c).map
        ((scalarAssoc T nrm a b ≪≫ eqToIso (congrArg (reductionDerivedChange T) hab)).hom.app K) ≫
      (scalarAssoc T nrm ab c ≪≫ eqToIso (congrArg (reductionDerivedChange T) hl)).hom.app K =
    (scalarAssoc T nrm b c ≪≫ eqToIso (congrArg (reductionDerivedChange T) hbc)).hom.app
        ((reductionDerivedChange T a).obj K) ≫
      (scalarAssoc T nrm a bc ≪≫ eqToIso (congrArg (reductionDerivedChange T) hr)).hom.app K := by
  subst ab
  subst bc
  subst abc
  simp only [eqToIso_refl, Iso.trans_refl]
  have hh := @Normalization.associative.{t + 1, t, t + 1, t + 2} T.ProEt inferInstance
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) inferInstance
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
    (WeilConjectures.integralCoefficientAbSheafify.{t, t} T)
    (fun Z ↦ reductionModulesHasDerivedCategory T Z)
    (fun {Z Z' : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
      (f : Z ⟶ Z') ↦ scalarPresentation T f) nrm R S V W a b c K
  simp only [eqToHom_refl, Category.comp_id] at hh
  simpa only [scalarAssoc, scalarPresentation] using hh

private theorem derivedCollapse_assoc (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V W : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : V ⟶ W)
    (ab : R ⟶ V) (bc : S ⟶ W) (abc : R ⟶ W)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) (K : reductionDerivedCategory T R) :
    (reductionDerivedChange T c).map
        ((derivedCollapse T nrm a b ab hab).hom.app K) ≫
      (derivedCollapse T nrm ab c abc hl).hom.app K =
    (derivedCollapse T nrm b c bc hbc).hom.app
        ((reductionDerivedChange T a).obj K) ≫
      (derivedCollapse T nrm a bc abc hr).hom.app K := by
  simp only [derivedCollapse_eq]
  exact scalarCollapse_assoc T nrm a b c ab bc abc hab hbc hl hr K

attribute [local irreducible] thetaN quotientAssociator

private theorem thetaN_associative (nrm : ScalarNormalization X)
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (K : d.derived Y) :
    (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
        ((thetaN d g nrm c b hbc).hom.app K) ≫
      (thetaN d g nrm b a hab).hom.app K =
    (quotientAssociator d nrm c b a hab hbc).hom.app ((N d g c).obj K) ≫
      (thetaN d g nrm c a (hab.trans hbc)).hom.app K := by
  simp only [thetaN_hom_app, quotientAssociator_hom_app]
  exact derivedCollapse_assoc X nrm (OrderedExchange.quotient d X c)
    (reductionCoefficientMap X d c b hbc) (reductionCoefficientMap X d b a hab)
    (OrderedExchange.quotient d X b) (reductionCoefficientMap X d c a (hab.trans hbc))
    (OrderedExchange.quotient d X a) (quotientComp d X c b hbc)
    (reductionCoefficientMap_comp X d c b a hab hbc) (quotientComp d X b a hab)
    (quotientComp d X c a (hab.trans hbc)) ((PulledReduction.source d g).obj K)

private theorem square (nrm : ScalarNormalization X) (nrmY : ScalarNormalization Y)
    (hq : QuotientCompatibility d g)
    (τ : ∀ n, N d g n ≅ H d g n)
    (hτ : ∀ n P, good Y (d.completedRing Y) P →
      (τ n).hom.app (DerivedCategory.Q.obj P) ≫ hCounit d g n P =
        nCounit d g n P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryTau d g n) (.up ℤ)).hom.app P))
    (b a : ℕ) (h : a ≤ b) (K : d.derived Y) :
    (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map ((τ b).hom.app K) ≫
      (thetaH d g hq b a h).app K =
        (thetaN d g nrm b a h).hom.app K ≫ (τ a).hom.app K := by
  unfold QuotientCompatibility at hq
  let q := reductionCoefficientMap X d b a h
  let F := reductionDerivedChange X q
  let α := Functor.whiskerRight (τ b).hom F ≫ thetaH d g hq b a h
  let β := (thetaN d g nrm b a h).hom ≫ (τ a).hom
  have he : α = β := by
    apply derived_natTrans_ext (B := reductionModules Y (d.completedRing Y))
      (D := reductionDerivedCategory X (d.finiteRing X a))
      _ _ (good Y (d.completedRing Y))
      (OrderedExchange.flatKFlatResolution Y (d.completedRing Y)) α β
    intro P hP
    have := (computed d g a P hP.1 hP.2).2
    let PN := ((ordinaryN d g b).mapHomologicalComplex (.up ℤ)).obj P
    let PH := ((ordinaryH d g b).mapHomologicalComplex (.up ℤ)).obj P
    let t := (NatIso.mapHomologicalComplex (ordinaryTau d g b) (.up ℤ)).hom.app P
    let s := (NatIso.mapHomologicalComplex (ordinaryTau d g a) (.up ℤ)).hom.app P
    let C := (reductionChange X q).mapHomologicalComplex (.up ℤ)
    let n := (NatIso.mapHomologicalComplex
      (ordinaryCollapse X nrm (OrderedExchange.quotient d X b) q
        (OrderedExchange.quotient d X a) (quotientComp d X b a h)) (.up ℤ)).hom.app
          (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P)
    let θ := (NatIso.mapHomologicalComplex (ordinaryTheta d g nrmY hq b a h)
      (.up ℤ)).hom.app P
    have hc : F.map (DerivedCategory.Q.map t) ≫
        reductionScalarComplexCounit X q PH =
      reductionScalarComplexCounit X q PN ≫ DerivedCategory.Q.map (C.map t) := by
      have hn := (complexCounitNat (reductionChange X q) F
        (reductionDerivedCounit X q)).naturality t
      simpa only [Functor.comp_map, complexCounitNat_app] using hn
    have ho := complexSquare (PulledReduction.ordinarySource d g)
      (reductionChange X (OrderedExchange.quotient d X b))
      (reductionChange X (OrderedExchange.quotient d X a))
      (ordinaryH d g b) (ordinaryH d g a) (reductionChange X q)
      (ordinaryCollapse X nrm (OrderedExchange.quotient d X b) q
        (OrderedExchange.quotient d X a) (quotientComp d X b a h)).hom
      (ordinaryTau d g b).hom (ordinaryTau d g a).hom
      (ordinaryTheta d g nrmY hq b a h).hom
      (ordinarySquare d g nrm nrmY hq b a h) P
    let QQ := DerivedCategory.Q (C := reductionModules X (d.finiteRing X a))
    have hq' := map_square_of_eq QQ (C.map t) θ n s ho
    exact squareOfRepresentatives
      (C := reductionDerivedCategory X (d.finiteRing X b))
      (D := reductionDerivedCategory X (d.finiteRing X a))
      F ((τ b).hom.app (DerivedCategory.Q.obj P))
      ((τ a).hom.app (DerivedCategory.Q.obj P))
      ((thetaN d g nrm b a h).hom.app (DerivedCategory.Q.obj P))
      ((thetaH d g hq b a h).app (DerivedCategory.Q.obj P))
      (nCounit d g b P) (hCounit d g b P) (nCounit d g a P) (hCounit d g a P)
      (reductionScalarComplexCounit X q PN) (reductionScalarComplexCounit X q PH)
      (DerivedCategory.Q.map t) (DerivedCategory.Q.map s)
      (DerivedCategory.Q.map n) (DerivedCategory.Q.map θ) (DerivedCategory.Q.map (C.map t))
      (hτ b P hP) (hτ a P hP) (thetaN_representative d g nrm b a h P hP _ rfl)
      (theta_representative d g nrmY hq b a h P hP.1 _ rfl) hc hq'
  exact congrArg (fun f ↦ f.app K) he

private theorem associative (nrm : ScalarNormalization X) (nrmY : ScalarNormalization Y)
    (hq : QuotientCompatibility d g) (τ : ∀ n, N d g n ≅ H d g n)
    (hτ : ∀ n P, good Y (d.completedRing Y) P →
      (τ n).hom.app (DerivedCategory.Q.obj P) ≫ hCounit d g n P =
        nCounit d g n P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryTau d g n) (.up ℤ)).hom.app P))
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (K : d.derived Y) :
    (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
        ((thetaH d g hq c b hbc).app K) ≫ (thetaH d g hq b a hab).app K =
      (quotientAssociator d nrm c b a hab hbc).hom.app ((H d g c).obj K) ≫
        (thetaH d g hq c a (hab.trans hbc)).app K := by
  unfold QuotientCompatibility at hq
  let F := reductionDerivedChange X (reductionCoefficientMap X d b a hab)
  let G := reductionDerivedChange X (reductionCoefficientMap X d c b hbc)
  let e := quotientAssociator d nrm c b a hab hbc
  apply (cancel_epi (F.map (G.map ((τ c).hom.app K)))).1
  rw [← Functor.map_comp_assoc]
  rw [square d g nrm nrmY hq τ hτ c b hbc K]
  simp only [F.map_comp, Category.assoc]
  rw [square d g nrm nrmY hq τ hτ b a hab K]
  rw [← Category.assoc, thetaN_associative d g nrm c b a hab hbc K]
  simp only [Category.assoc]
  have hn := e.hom.naturality ((τ c).hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [square d g nrm nrmY hq τ hτ c a (hab.trans hbc) K]

private theorem unit (nrmY : ScalarNormalization Y) (hq : QuotientCompatibility d g)
    (a : ℕ) (K : d.derived Y) :
    (thetaH d g hq a a (le_refl a)).app K =
      (derivedIdentity X (R := d.finiteRing X a)
        (reductionCoefficientMap X d a a (le_refl a))
        (reductionCoefficientMap_id X d a)).hom.app ((H d g a).obj K) := by
  unfold QuotientCompatibility at hq
  let e := derivedIdentity X (R := d.finiteRing X a)
        (reductionCoefficientMap X d a a (le_refl a))
    (reductionCoefficientMap_id X d a)
  have he : thetaH d g hq a a (le_refl a) = Functor.whiskerLeft (H d g a) e.hom := by
    apply derived_natTrans_ext (B := reductionModules Y (d.completedRing Y))
      (D := reductionDerivedCategory X (d.finiteRing X a))
      _ _ (good Y (d.completedRing Y))
      (OrderedExchange.flatKFlatResolution Y (d.completedRing Y))
    intro P hP
    have := (computed d g a P hP.1 hP.2).2
    let q := reductionCoefficientMap X d a a (le_refl a)
    let PP := ((ordinaryH d g a).mapHomologicalComplex (.up ℤ)).obj P
    let u := (NatIso.mapHomologicalComplex (ordinaryIdentity X
      (R := d.finiteRing X a) q (reductionCoefficientMap_id X d a)) (.up ℤ)).hom.app PP
    have ho : (NatIso.mapHomologicalComplex
        (ordinaryTheta d g nrmY hq a a (le_refl a)) (.up ℤ)).hom.app P = u := by
      apply HomologicalComplex.hom_ext
      intro i
      exact ordinaryTheta_unit d g nrmY hq a (P.X i)
    have hθ := theta_representative d g nrmY hq a a (le_refl a) P hP.1 _ rfl
    rw [ho] at hθ
    exact unitOfRepresentative (reductionDerivedChange X q) e.hom
      (hCounit d g a P) ((thetaH d g hq a a (le_refl a)).app (DerivedCategory.Q.obj P))
      (reductionScalarComplexCounit X q PP) (DerivedCategory.Q.map u) hθ
      (derivedIdentity_rep X q (reductionCoefficientMap_id X d a) PP)
  exact congrArg (fun f ↦ f.app K) he

end

end AlgebraicGeometry.Scheme.PulledNormalization
