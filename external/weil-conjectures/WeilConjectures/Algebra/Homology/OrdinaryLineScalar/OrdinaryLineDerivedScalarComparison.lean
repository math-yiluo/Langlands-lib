/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarPresentations
public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarLineData
import all WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarLineData
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarBalancedComparison
import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarFlatDescent
import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarEvaluation
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
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # Ordinary signed-line tensor and derived scalar extension

Source: Stacks Project, Tags 07A4, 0G7E and 0D6D; blueprint main-20261015,
Tate-twist local freeness, proof (3).
(blueprint: lem-pur-ordinary-line-derived-scalar-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t a w u v b r ua va
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
-- Prefer the native additive structures over routes through abelian instances.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
namespace SheafOfModules.OrdinaryLineScalar

variable (X : Scheme.{t}) [EssentiallySmall.{max a (t + 1)} X.ProEt]

variable {X}
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
attribute [local irreducible] LineUnbounded.derived LineUnbounded.normalization
  KFlatFixedTensor.representativeIso compute signedLinePower scalarTensorPower
  LineUnbounded.cancellation
  LineUnbounded.pureTensor ScalarHomOrdinary.pure

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] monoidalCategory scalar

section ScalarTowerProof

private theorem scalar_eq_sectionTensor
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    {α : R ⟶ S} (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    scalar.{t, a, w} p M U s x =
      SuccessiveDerivedQuotient.sectionTensor p M U s x := by
  unfold scalar
  rfl

private def computation
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    {α : R ⟶ S} (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α) :
    𝒬[R] ⋙ p.derived ⟶ p.ordinary.mapHomologicalComplex (.up ℤ) ⋙ 𝒬[S] :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules.{t, a} X R)).inv
      p.derived ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (Modules.{t, a} X R) (.up ℤ)) p.counit ≫
    Functor.whiskerLeft (p.ordinary.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (Modules.{t, a} X S)).hom

attribute [local irreducible] computation

section OrdinaryCore

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)]

end OrdinaryCore

end ScalarTowerProof

/-- The ordinary derived scalar comparison, normalized on flat-term K-flat models,
including its inverse, arbitrary-derived-morphism naturality and evaluation square.
Source: Stacks 07A4, 0G7E and blueprint proof (3)
(blueprint: lem-pur-ordinary-line-derived-scalar-comparison).
Proof: (1) trivialize the lines and identify signed opposite powers by actual dual
 evaluation. (2) exact line tensor is termwise on unbounded complexes by the preceding
 theorem. (3) reassociate the total tensor and use exactness and preservation of sums
 to show P tensor M remains K-flat with flat terms. (4) ringed-topos K-flat pullback
 for the identity topos proves the same for P tensor S, even for nonflat R to S.
 (5) the displayed balanced formula defines a sheaf map, with inverse reassociation
 after B inverse. Balancing moves r to alpha(r); both composites fix generators.
 The same formula commutes with differentials and chain maps and with homotopies.
 (6) site derived tensor descent and localization's universal property descend this
 natural chain isomorphism and its inverse. Naturality for roofs follows by inverting
 the quasi-isomorphism leg, so the result is independent of representatives.
 (7) tower coherence is the signed-power tower identity on generators.
 (8) evaluation compatibility sends both paths to p tensor s alpha(ev(l,phi)).
 (9) identity multiplication sends both paths to sp tensor l. For an arbitrary line
 automorphism the normalized map is tensor by that automorphism, including negative
 and zero exponents. No completeness, boundedness or flat coefficient map is used. -/
theorem ordinary_line_derived_scalar_comparison
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (L : Modules.{t, a} X R) (K : Modules.{t, a} X S)
    [L.IsFiniteLocallyFreeOfRank 1] [K.IsFiniteLocallyFreeOfRank 1]
    (l : LineData L) (k : LineData K)
    (b : changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α L ≅ K)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α (power.{t, a} L m) ≅ power.{t, a} K m)
    (hB : SignedLineComparisonNormalized.{t + 1, t, a} α L K b B) :
    Nonempty (Comparison p L K l k B) := by
  classical
  obtain ⟨o, ho, hi⟩ := ordinary_scalar_line_balanced α p L K B
  obtain ⟨d, hd⟩ := ordinary_scalar_line_flat_descent α p L K l k o
  refine ⟨{
    ordinary := o
    hom_formula := ho
    inv_formula := hi
    derived := d
    extended_flat := ?_
    representative := hd
    evaluation := ordinary_scalar_line_evaluation α p L K B l k b hB o ho d hd
  }⟩
  intro P hP
  exact isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (SuccessiveDerivedQuotient.identityInverse R) α p.ordinary p.obj_eq p.map_eq P hP.1 hP.2

set_option backward.isDefEq.respectTransparency.types true

private theorem localized_unit_square
    {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) (T S E : C ⥤ C) (F G H : D ⥤ D)
    (f : Q ⋙ F ≅ T ⋙ Q) (g : Q ⋙ G ≅ S ⋙ Q)
    (e : E ≅ 𝟭 C) (u : H ≅ 𝟭 D) (d : F ⋙ H ≅ H ⋙ G)
    (v : ∀ P : C, H.obj (Q.obj P) ⟶ Q.obj (E.obj P))
    (o : T ⋙ E ≅ E ⋙ S) (a : T ⟶ S)
    (hu : ∀ P, u.hom.app (Q.obj P) = v P ≫ Q.map (e.hom.app P))
    (ho : ∀ P, o.hom.app P ≫ S.map (e.hom.app P) =
      e.hom.app (T.obj P) ≫ a.app P)
    (P : C)
    (hd : d.hom.app (Q.obj P) ≫ G.map (v P) ≫ g.hom.app (E.obj P) =
      H.map (f.hom.app P) ≫ v (T.obj P) ≫ Q.map (o.hom.app P)) :
    u.inv.app (F.obj (Q.obj P)) ≫ d.hom.app (Q.obj P) ≫
      G.map (u.hom.app (Q.obj P)) ≫ g.hom.app P =
        f.hom.app P ≫ Q.map (a.app P) := by
  apply (cancel_epi (u.hom.app (F.obj (Q.obj P)))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  calc
    d.hom.app (Q.obj P) ≫ G.map (u.hom.app (Q.obj P)) ≫ g.hom.app P =
        d.hom.app (Q.obj P) ≫ G.map (v P) ≫
          g.hom.app (E.obj P) ≫ Q.map (S.map (e.hom.app P)) := by
      rw [hu P, G.map_comp]
      simp only [Category.assoc]
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc] using
        congrArg (fun z ↦ d.hom.app (Q.obj P) ≫ G.map (v P) ≫ z)
          (g.hom.naturality (e.hom.app P))
    _ = H.map (f.hom.app P) ≫ v (T.obj P) ≫ Q.map (o.hom.app P) ≫
        Q.map (S.map (e.hom.app P)) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ Q.map (S.map (e.hom.app P))) hd
    _ = H.map (f.hom.app P) ≫ u.hom.app (Q.obj (T.obj P)) ≫
        Q.map (a.app P) := by
      rw [← Q.map_comp, ho P, Q.map_comp, hu (T.obj P)]
      simp only [Category.assoc]
    _ = u.hom.app (F.obj (Q.obj P)) ≫ f.hom.app P ≫ Q.map (a.app P) := by
      simpa only [Functor.id_map, Functor.comp_obj, Category.assoc] using
        congrArg (fun z ↦ z ≫ Q.map (a.app P)) (u.hom.naturality (f.hom.app P))

private theorem localized_unit_cochain
    {A D : Type*} [Category A] [Abelian A] [Category D]
    (Q : CochainComplex A ℤ ⥤ D) (T S E : A ⥤ A)
    [T.Additive] [S.Additive] [E.Additive] (F G H : D ⥤ D)
    (f : Q ⋙ F ≅ T.mapHomologicalComplex (.up ℤ) ⋙ Q)
    (g : Q ⋙ G ≅ S.mapHomologicalComplex (.up ℤ) ⋙ Q)
    (e₀ : E ≅ 𝟭 A) (u : H ≅ 𝟭 D) (d : F ⋙ H ≅ H ⋙ G)
    (v : ∀ P, H.obj (Q.obj P) ⟶ Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (o₀ : T ⋙ E ≅ E ⋙ S) (a₀ : T ⟶ S)
    (hu : ∀ P, u.hom.app (Q.obj P) = v P ≫ Q.map
      ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerLeft (𝟭 _) e₀ ≪≫ Functor.leftUnitor _) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P))
    (ho₀ : ∀ M, o₀.hom.app M ≫ S.map (e₀.hom.app M) =
      e₀.hom.app (T.obj M) ≫ a₀.app M)
    (Good : CochainComplex A ℤ → Prop)
    (hd : ∀ P, Good P →
      d.hom.app (Q.obj P) ≫ G.map (v P) ≫
        g.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      H.map (f.hom.app P) ≫ v ((T.mapHomologicalComplex (.up ℤ)).obj P) ≫
        Q.map ((Functor.mapHomologicalComplexCompIso o₀ (.up ℤ)).hom.app P))
    (resolve : ∀ P, ∃ (P' : CochainComplex A ℤ) (r : P' ⟶ P),
      Good P' ∧ IsIso (Q.map r)) :
    ∀ P, u.inv.app (F.obj (Q.obj P)) ≫ d.hom.app (Q.obj P) ≫
      G.map (u.hom.app (Q.obj P)) ≫ g.hom.app P =
        f.hom.app P ≫ Q.map ((NatTrans.mapHomologicalComplex a₀ (.up ℤ)).app P) := by
  let T' := T.mapHomologicalComplex (.up ℤ)
  let S' := S.mapHomologicalComplex (.up ℤ)
  let E' := E.mapHomologicalComplex (.up ℤ)
  let e : E' ≅ 𝟭 (CochainComplex A ℤ) :=
    Functor.mapHomologicalComplexCompIso
      (Functor.isoWhiskerLeft (𝟭 _) e₀ ≪≫ Functor.leftUnitor _) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso A (.up ℤ)
  let o : T' ⋙ E' ≅ E' ⋙ S' :=
    Functor.mapHomologicalComplexCompIso o₀ (.up ℤ)
  let a : T' ⟶ S' := NatTrans.mapHomologicalComplex a₀ (.up ℤ)
  have he_f (P : CochainComplex A ℤ) (i : ℤ) :
      (e.hom.app P).f i = e₀.hom.app (P.X i) := by
    change (e₀.hom.app (P.X i) ≫ 𝟙 _) ≫ 𝟙 _ = _
    simp only [Category.comp_id]
  have ho (P : CochainComplex A ℤ) :
      o.hom.app P ≫ S'.map (e.hom.app P) = e.hom.app (T'.obj P) ≫ a.app P := by
    apply HomologicalComplex.Hom.ext
    funext i
    change o₀.hom.app (P.X i) ≫ S.map ((e.hom.app P).f i) =
      (e.hom.app (T'.obj P)).f i ≫ a₀.app (P.X i)
    rw [he_f, he_f]
    exact ho₀ (P.X i)
  let lhs : Q ⋙ F ⟶ S' ⋙ Q :=
    Functor.whiskerLeft (Q ⋙ F) u.inv ≫ Functor.whiskerLeft Q d.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft Q u.hom) G ≫ g.hom
  let rhs : Q ⋙ F ⟶ S' ⋙ Q := f.hom ≫ Functor.whiskerRight a Q
  intro P
  obtain ⟨P', r, hp, hr⟩ := resolve P
  let := hr
  have : IsIso ((Q ⋙ F).map r) := by
    change IsIso (F.map (Q.map r))
    infer_instance
  have he : lhs.app P' = rhs.app P' :=
    localized_unit_square Q T' S' E' F G H f g e u d v o a hu ho P' (hd P' hp)
  change lhs.app P = rhs.app P
  apply (cancel_epi ((Q ⋙ F).map r)).1
  rw [lhs.naturality, rhs.naturality, he]

private theorem ordinary_unit_tensor
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})
    (E : scalarModules J R ⥤ scalarModules J R) (e : E ≅ 𝟭 (scalarModules J R))
    (insert : ∀ (M : scalarModules J R) (U : Cᵒᵖ),
      M.val.obj U → (E.obj M).val.obj U)
    (hi : ∀ M U x, (e.hom.app M).val.app U (insert M U x) = x)
    (M N K : scalarModules J R) (a : N ⟶ K)
    (c : E.obj ((monoidalCategory R).tensorObj M N) ⟶
      (monoidalCategory R).tensorObj (E.obj M) K)
    (hc : ∀ U x y, c.val.app U
      (insert ((monoidalCategory R).tensorObj M N) U
        (ScalarHomOrdinary.pure R M N U x y)) =
      ScalarHomOrdinary.pure R (E.obj M) K U (insert M U x) (a.val.app U y)) :
    c ≫ (monoidalCategory R).whiskerRight (e.hom.app M) K =
      e.hom.app ((monoidalCategory R).tensorObj M N) ≫
        (monoidalCategory R).whiskerLeft M a := by
  let : MonoidalCategory (scalarModules J R) := monoidalCategory R
  change c ≫ (e.hom.app M ▷ K) = e.hom.app (M ⊗ N) ≫ M ◁ a
  rw [← tensorHom_id (e.hom.app M) K, ← id_tensorHom M a]
  have hinv (H : scalarModules J R) (U : Cᵒᵖ) (x : H.val.obj U) :
      (e.inv.app H).val.app U x = insert H U x := by
    nth_rw 1 [← hi H U x]
    exact congrArg (fun f ↦ f.val.app U (insert H U x)) (e.hom_inv_id_app H)
  apply (cancel_epi (e.inv.app (M ⊗ N))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply ScalarHomOrdinary.pure_hom_ext R M N (M ⊗ K)
  intro U x y
  change ((e.hom.app M ⊗ₘ 𝟙 K).val.app U)
    (c.val.app U ((e.inv.app (M ⊗ N)).val.app U
      (ScalarHomOrdinary.pure R M N U x y))) = _
  rw [hinv, hc, ScalarHomOrdinary.pure_map, hi]
  simpa only [Functor.id_obj, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using (ScalarHomOrdinary.pure_map R (𝟙 M) a U x y).symm

set_option backward.isDefEq.respectTransparency.types false

private theorem ordinary_identity_normalized
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
      (α : R ⟶ S), SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
        (J := Scheme.ProEt.topology X) α)
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (u : UnitData p R) (L K : Modules.{t, a} X R) (l : LineData L) (k : LineData K)
    (B : ∀ m : ℤ,
      changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
        (J := Scheme.ProEt.topology X) (𝟙 R) (power.{t, a} L m) ≅ power.{t, a} K m)
    (A : ∀ m : ℤ, power.{t, a} L m ≅ power.{t, a} K m)
    (hA : ∀ (m : ℤ) (U : X.ProEtᵒᵖ) (s : R.obj.obj U) (x : (power.{t, a} L m).val.obj U),
      (B m).hom.val.app U (scalarExtensionSection (𝟙 R) (power.{t, a} L m) U s x) =
        s • (A m).hom.val.app U x)
    (c : Comparison (p (𝟙 R)) L K l k B) (m : ℤ) (M : Modules.{t, a} X R) :
    (c.ordinary m).hom.app M ≫ (tensor.{t, a} K m).map (u.ordinary.hom.app M) =
      u.ordinary.hom.app ((tensor.{t, a} L m).obj M) ≫ M ◁ (A m).hom := by
  set_option backward.isDefEq.respectTransparency.types true in
    apply ordinary_unit_tensor R (p (𝟙 R)).ordinary u.ordinary
      (fun M U x ↦ scalar.{t, a, w} (p (𝟙 R)) M U 1 x)
      (fun M U x ↦ by simpa only [one_smul] using u.formula M U 1 x)
      M (power.{t, a} L m) (power.{t, a} K m) (A m).hom ((c.ordinary m).hom.app M)
    intro U x y
    rw [← pure_eq_ordinary.{t, a} (X := X) M (power.{t, a} L m) U x y,
      ← pure_eq_ordinary.{t, a} (X := X) ((p (𝟙 R)).ordinary.obj M)
        (power.{t, a} K m) U (scalar.{t, a, w} (p (𝟙 R)) M U 1 x)
        ((A m).hom.val.app U y)]
    change ((c.ordinary m).hom.app M).val.app U
      (scalar.{t, a, w} (p (𝟙 R)) ((tensor.{t, a} L m).obj M) U 1
        (LineUnbounded.pureTensor.{t, a} X R M (power.{t, a} L m) U x y)) = _
    rw [c.hom_formula, hA]
    simp only [one_smul]
    set_option backward.isDefEq.respectTransparency.types false in rfl

/-- Over an identical coefficient ring an arbitrary line comparison remains its actual
signed-power tensor map after scalar-unitor normalization; it need not be identity.
Source: blueprint proof (3), Stacks 03EK and 07A4
(blueprint: lem-pur-ordinary-line-derived-scalar-comparison).
Proof: insert the inverse scalar multiplication at the source and multiplication at
the target. On generators the comparison then sends p tensor l to p tensor a_m(l).
It is therefore the termwise tensor natural transformation displayed below. Apply the
representative and scalar-unitor equations on flat-term K-flat complexes and paste
using naturality. For an arbitrary complex, naturality along a flat-term K-flat
resolution and cancellation of its invertible derived image give the formula.
No sign or bound is involved. -/
theorem comparison_identity_arbitrary
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
      (α : R ⟶ S), SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
        (J := Scheme.ProEt.topology X) α)
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (u : UnitData p R) (L K : Modules.{t, a} X R) (l : LineData L) (k : LineData K)
    (B : ∀ m : ℤ,
      changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
        (J := Scheme.ProEt.topology X) (𝟙 R) (power.{t, a} L m) ≅ power.{t, a} K m)
    (A : ∀ m : ℤ, power.{t, a} L m ≅ power.{t, a} K m)
    (hA : ∀ (m : ℤ) (U : X.ProEtᵒᵖ) (s : R.obj.obj U) (x : (power.{t, a} L m).val.obj U),
      (B m).hom.val.app U (scalarExtensionSection (𝟙 R) (power.{t, a} L m) U s x) =
        s • (A m).hom.val.app U x)
    (c : Comparison (p (𝟙 R)) L K l k B) :
    ∀ (m : ℤ) (P : CochainComplex (Modules.{t, a} X R) ℤ),
      u.derived.inv.app ((twist.{t, a, w} L m).obj (𝒬[R].obj P)) ≫
        (c.derived m).hom.app (𝒬[R].obj P) ≫
        (twist.{t, a, w} K m).map (u.derived.hom.app (𝒬[R].obj P)) ≫
        (k.factors m).hom.app P =
      (l.factors m).hom.app P ≫ 𝒬[R].map
        ((NatTrans.mapHomologicalComplex
          ((tensoringRight (Modules.{t, a} X R)).map (A m).hom) (.up ℤ)).app P) := by
  set_option backward.isDefEq.respectTransparency.types true in
    intro m
    apply localized_unit_cochain 𝒬[R] (tensor.{t, a} L m) (tensor.{t, a} K m)
      (p (𝟙 R)).ordinary (twist.{t, a, w} L m) (twist.{t, a, w} K m)
      (p (𝟙 R)).derived (l.factors m) (k.factors m) u.ordinary u.derived
      (c.derived m) (compute.{t, a, w} (p (𝟙 R))) (c.ordinary m)
      ((tensoringRight (Modules.{t, a} X R)).map (A m).hom) u.computed
      (ordinary_identity_normalized p u L K l k B A hA c m) FlatModel
      (c.representative m)
    intro P
    obtain ⟨P', f, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
    refine ⟨P', f, ⟨hp, fun i ↦ ?_⟩, ?_⟩
    · exact (exactFunctor _ _).prop_of_iso
        (siteSheafTensorRightIso R (P'.X i)).symm (hf i)
    · exact (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules.{t, a} X R) f).2 hq

/-- The multiplication line datum gives the scalar-unitor equation on every derived object.
Source: blueprint proof (3), Stacks 03EK and 06YY
(blueprint: lem-pur-ordinary-line-derived-scalar-comparison).
Proof: the signed-line identity theorem gives B_m(l tensor s) = sl for every sign.
Both chain-level paths send (p tensor l) tensor s to sp tensor l. The balanced
universal property and localization's faithfulness give the equation for all objects. -/
theorem comparison_identity
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
      (α : R ⟶ S), SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
        (J := Scheme.ProEt.topology X) α)
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (u : UnitData p R) (L : Modules.{t, a} X R) (l : LineData L)
    (B : ∀ m : ℤ,
      changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
        (J := Scheme.ProEt.topology X) (𝟙 R) (power.{t, a} L m) ≅ power.{t, a} L m)
    (hB : ∀ (m : ℤ) (U : X.ProEtᵒᵖ) (s : R.obj.obj U) (x : (power.{t, a} L m).val.obj U),
      (B m).hom.val.app U (scalarExtensionSection (𝟙 R) (power.{t, a} L m) U s x) = s • x)
    (c : Comparison (p (𝟙 R)) L L l l B) :
    ∀ (m : ℤ) (Y : DerivedCategory (Modules.{t, a} X R)),
      (c.derived m).hom.app Y ≫ (twist.{t, a, w} L m).map (u.derived.hom.app Y) =
        u.derived.hom.app ((twist.{t, a, w} L m).obj Y) := by
  set_option backward.isDefEq.respectTransparency.types true in
    intro m
    let left : twist.{t, a, w} L m ⋙ (p (𝟙 R)).derived ⟶ twist.{t, a, w} L m :=
      (c.derived m).hom ≫ Functor.whiskerRight u.derived.hom (twist.{t, a, w} L m)
    let right : twist.{t, a, w} L m ⋙ (p (𝟙 R)).derived ⟶ twist.{t, a, w} L m :=
      Functor.whiskerLeft (twist.{t, a, w} L m) u.derived.hom
    have h : left = right := by
      apply Localization.natTrans_ext 𝒬[R]
        (HomologicalComplex.quasiIso (Modules.{t, a} X R) (.up ℤ))
      intro P
      have hh := comparison_identity_arbitrary p u L L l l B
        (fun _ ↦ Iso.refl _) (by simpa using hB) c m P
      have hi : (NatTrans.mapHomologicalComplex
          ((tensoringRight (Modules.{t, a} X R)).map (Iso.refl (power.{t, a} L m)).hom)
          (.up ℤ)).app P = 𝟙 _ := by
        simp only [Iso.refl_hom]
        erw [(tensoringRight (Modules.{t, a} X R)).map_id,
          NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
      erw [hi, CategoryTheory.Functor.map_id, Category.comp_id] at hh
      apply (cancel_mono ((l.factors m).hom.app P)).1
      apply (cancel_epi (u.derived.inv.app ((twist.{t, a, w} L m).obj (𝒬[R].obj P)))).1
      simpa [left, right, Category.assoc] using hh
    intro Y
    simpa [left, right] using congrArg (fun z ↦ z.app Y) h

end SheafOfModules.OrdinaryLineScalar
