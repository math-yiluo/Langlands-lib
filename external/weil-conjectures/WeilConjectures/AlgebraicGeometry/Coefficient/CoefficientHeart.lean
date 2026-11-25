/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCurveLisseDescent
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCurveComplement
import WeilConjectures.AlgebraicGeometry.SixFunctors.StratificationGenericNeighborhood
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The constructible coefficient heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart,
_section.md and sk-lem-coefficient-heart.proof.md (blueprint: lemma-constructible-sheaves).

All module categories use the actual condensed coefficient ring pulled back from the point.
Constructibility is the finite constant scalar model predicate, and locally closed extension
is the previously constructed open extension into the scheme-theoretic closure followed by
closed direct image. The assertion predicates below spell out the clauses of the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The curve specialization: the actual open counit and complementary closed unit give
its short exact sequence. The closed term restricts to zero on the dense lisse open.
Source: blueprint lemma-constructible-sheaves, final paragraph
(blueprint: lemma-constructible-sheaves). -/
def CoefficientHeartCurveAssertions (X : Scheme.{u}) : Prop :=
  topologicalKrullDim X ≤ 1 →
  ∀ F : ConstantModelConstructible Λ X,
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ U.ι).obj F.obj) ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
        Set.range i = (U : Set X)ᶜ ∧
        ((U : Set X)ᶜ).Finite ∧
        (∀ x ∈ (U : Set X)ᶜ, IsClosed ({x} : Set X)) ∧
        Mono ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app
          F.obj) ∧
        Epi ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app F.obj) ∧
        (ComposableArrows.mk₂
          ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app F.obj)
          ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app F.obj)).Exact ∧
        IsZero ((CondensedRing.upperStar Λ U.ι).obj
          ((CondensedRing.lowerStar Λ i).obj ((CondensedRing.upperStar Λ i).obj F.obj)))

/-- A finite, non-strict filtration of each constructible sheaf by subsheaves, with the
specified locally closed extensions as successive quotients. Zero and empty filtrations
are allowed. Source: blueprint lemma-constructible-sheaves, clause (3)
(blueprint: lemma-constructible-sheaves). -/
def CoefficientHeartFiltrationAssertions (X : Scheme.{u}) [IsNoetherian X] : Prop :=
  ∀ F : ConstantModelConstructible Λ X,
    ∃ (m : ℕ) (T : Fin (m + 1) → Subobject F.obj), T 0 = ⊥ ∧ T (Fin.last m) = ⊤ ∧
      ∃ h : ∀ a : Fin m, T a.castSucc ≤ T a.succ,
        ∀ a : Fin m, ∃ (S : Scheme.{u}) (j : S ⟶ X) (hj : IsImmersion j)
          (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
          IsLisseCoefficientModule Λ L ∧
          Nonempty (cokernel (Subobject.ofLE (T a.castSucc) (T a.succ) (h a)) ≅
            (coefficientHeartLocallyClosedExtension Λ j hj).obj L)

/-- Exactness of both factors in extension through the scheme-theoretic closure, exactness
of their composite, and descent by applying this composite termwise to complexes.
Source: blueprint lemma-constructible-sheaves, introductory locally closed extension paragraph
(blueprint: lemma-constructible-sheaves). -/
def CoefficientHeartExtensionAssertions (X : Scheme.{u}) [IsNoetherian X] : Prop :=
  ∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a),
    letI : IsImmersion a := ha
    letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
    PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ a.toImage) ∧
    PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ a.toImage) ∧
    PreservesFiniteLimits (CondensedRing.lowerStar Λ a.imageι) ∧
    PreservesFiniteColimits (CondensedRing.lowerStar Λ a.imageι) ∧
    PreservesFiniteLimits (coefficientHeartLocallyClosedExtension Λ a ha) ∧
    PreservesFiniteColimits (coefficientHeartLocallyClosedExtension Λ a ha) ∧
    Exists fun [_hadd : (coefficientHeartLocallyClosedExtension Λ a ha).Additive] ↦
    ∃ D : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) ⥤
          DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      Nonempty (DerivedCategory.Q ⋙ D ≅
        (coefficientHeartLocallyClosedExtension Λ a ha).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q)

/-- Every assertion of the constructible-heart node, including its introductory derived
and locally closed extension clauses. Exact descent is characterized by the localization
square with the termwise functor, so no arbitrary derived map is substituted.
Source: blueprint lemma-constructible-sheaves, introduction, clauses (1)--(3), final paragraph
(blueprint: lemma-constructible-sheaves). -/
def CoefficientHeartAssertions (X : Scheme.{u}) [IsNoetherian X] : Prop :=
  ((constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _) =
    constantModelBoundedConstructible Λ X) ∧
  (∀ (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) (n : ℤ),
    constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ X ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      constantModelBoundedConstructible Λ X ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
  (∀ F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    IsConstantModelConstructible Λ X F ↔
      ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
        IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (R.immersion a)).obj F)) ∧
  CoefficientHeartExtensionAssertions Λ X ∧
  (∀ (F G : ConstantModelConstructible Λ X) (f : F.obj ⟶ G.obj),
    IsConstantModelConstructible Λ X (kernel f) ∧
      IsConstantModelConstructible Λ X (cokernel f)) ∧
  (∀ (F G : ConstantModelConstructible Λ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : F.obj ⟶ M) (g : M ⟶ G.obj),
    Mono f → Epi g → (ComposableArrows.mk₂ f g).Exact →
      IsConstantModelConstructible Λ X M) ∧
  Nonempty (Abelian (ConstantModelConstructible Λ X)) ∧
  PreservesFiniteLimits (ObjectProperty.ι (IsConstantModelConstructible Λ X)) ∧
  PreservesFiniteColimits (ObjectProperty.ι (IsConstantModelConstructible Λ X)) ∧
  EssentiallySmall.{u + 1} (ConstantModelConstructible Λ X) ∧
  CoefficientHeartFiltrationAssertions Λ X ∧ CoefficientHeartCurveAssertions Λ X

/-- Keep the image construction abstract while assembling a filtration. -/
private def heartFiltrationImage {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : Y.Opens) : Subobject M :=
  imageSubobject (coefficientHeartOpenCounit Λ M V)

private theorem heartFiltrationImage_eq {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : Y.Opens) : heartFiltrationImage Λ M V = coefficientHeartFiltrationStep Λ M V := rfl

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp

/-- Lissity descends across the closed side of a commuting pullback square. -/
private theorem heartLisse_closed_square {Y S W T : Scheme.{u}}
    (a : W ⟶ Y) (b : S ⟶ Y) (t : T ⟶ W) (r : T ⟶ S)
    [IsClosedImmersion t] [Surjective t] (hsq : t ≫ a = r ≫ b)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ b).obj M)) :
    IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ a).obj M) := by
  have h := IsLocallyFree.upperStar Λ r ((isLocallyFree_iff _).2 hM)
  let e := ((CondensedRing.upperStarComp Λ t a).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) hsq) ≪≫
    (CondensedRing.upperStarComp Λ r b).app M
  exact (coefficientHeart_curve_lisse_descent.{u, u} Λ t _).1.mpr
    ((isLocallyFree_iff _).1 (h.of_iso e.symm))

/-- Lissity descends across the closed side of a commuting pullback square. -/
private theorem heartLisse_closed_square_coefficient
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)] {Y S W T : Scheme.{u}}
    (a : W ⟶ Y) (b : S ⟶ Y) (t : T ⟶ W) (r : T ⟶ S)
    [IsClosedImmersion t] [Surjective t] (hsq : t ≫ a = r ≫ b)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj L) Y))
    (hM : IsLisseCoefficientModule (coefficientHeartRingObj L)
      ((CondensedRing.upperStar (coefficientHeartRingObj L) b).obj M)) :
    IsLisseCoefficientModule (coefficientHeartRingObj L)
      ((CondensedRing.upperStar (coefficientHeartRingObj L) a).obj M) :=
  heartLisse_closed_square (coefficientHeartRingObj L) a b t r hsq M hM

-- Abstract the predicate before rewriting cover projections under inverse images.
private def heartLissePullback {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) : Prop :=
  IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M)

private theorem heartLissePullback_eq {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    heartLissePullback Λ f M =
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M) := rfl

private theorem heartLissePullback_comp {Y Z T : Scheme.{u}} (f : T ⟶ Z) (g : Z ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    heartLissePullback Λ (f ≫ g) M →
      heartLissePullback Λ f ((CondensedRing.upperStar Λ g).obj M) := by
  intro h
  exact (isLocallyFree_iff _).1
    (((isLocallyFree_iff _).2 h).of_iso ((CondensedRing.upperStarComp Λ f g).app M))

private theorem heartLissePullback_cover {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (h : ∀ c, heartLissePullback Λ (C.f c ≫ g) M) : heartLissePullback Λ g M := by
  exact (isLocallyFree_iff _).1 (CondensedRing.locFree_of_cover _ C fun c ↦
    (isLocallyFree_iff _).2 (heartLissePullback_comp Λ (C.f c) g M (h c)))

attribute [local irreducible] heartLissePullback

set_option backward.isDefEq.respectTransparency true in
private theorem heartLisse_iSup {Y : Scheme.{u}} {I : Type u} (W : I → Y.Opens)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hW : ∀ c, IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (W c).ι).obj M)) :
    IsLisseCoefficientModule Λ
      ((CondensedRing.upperStar Λ (⨆ c, W c).ι).obj M) := by
  simp only [← heartLissePullback_eq] at hW ⊢
  have hv (c : I) :
      Y.homOfLE (le_iSup W c) ≫ (⨆ c, W c : Y.Opens).ι = (W c).ι := Y.homOfLE_ι _
  let C : (⨆ c, W c : Y.Opens).toScheme.OpenCover := Scheme.Cover.mkOfCovers I
    (fun c ↦ (W c).toScheme) (fun c ↦ Y.homOfLE (le_iSup W c)) (by
    intro x
    obtain ⟨c, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
    refine ⟨c, ⟨x.val, hx⟩, ?_⟩
    rw [Scheme.homOfLE_apply']
    exact Subtype.ext rfl)
  let D : Scheme.Cover.{u} Scheme.proetalePrecoverage (⨆ c, W c : Y.Opens).toScheme :=
    { I₀ := I
      X := fun c ↦ (W c).toScheme
      f := (fun c ↦ Y.homOfLE (le_iSup W c))
      mem₀ := Scheme.zariskiPrecoverage_le_proetalePrecoverage _ C.mem₀ }
  apply heartLissePullback_cover Λ (⨆ c, W c : Y.Opens).ι D M
  intro c
  change heartLissePullback Λ (Y.homOfLE (le_iSup W c) ≫ (⨆ c, W c : Y.Opens).ι) M
  rw [hv]
  exact hW c

private theorem heartLisse_iSup_coefficient
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)] {Y : Scheme.{u}} {I : Type u}
    (W : I → Y.Opens)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj L) Y))
    (hW : ∀ c, IsLisseCoefficientModule (coefficientHeartRingObj L)
      ((CondensedRing.upperStar (coefficientHeartRingObj L) (W c).ι).obj M)) :
    IsLisseCoefficientModule (coefficientHeartRingObj L)
      ((CondensedRing.upperStar (coefficientHeartRingObj L) (⨆ c, W c).ι).obj M) :=
  heartLisse_iSup (coefficientHeartRingObj L) W M hW

/-- The complement with its actual reduced induced closed scheme structure. -/
private def heartComplement {Y : Scheme.{u}} (U : Y.Opens) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩).subscheme

private def heartComplementι {Y : Scheme.{u}} (U : Y.Opens) : heartComplement U ⟶ Y :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩).subschemeι

private instance heartComplement_closed {Y : Scheme.{u}} (U : Y.Opens) :
    IsClosedImmersion (heartComplementι U) := by
  unfold heartComplementι
  infer_instance

private instance heartComplement_reduced {Y : Scheme.{u}} (U : Y.Opens) :
    IsReduced (heartComplement U) := by
  unfold heartComplement
  infer_instance

private theorem heartComplement_range {Y : Scheme.{u}} (U : Y.Opens) :
    Set.range (heartComplementι U) = (U : Set Y)ᶜ := by
  change Set.range
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩).subschemeι = (U : Set Y)ᶜ
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

attribute [local irreducible] heartFiltrationImage
  CondensedRing.upperStarLowerStarAdjunction coefficientHeartLocallyClosedExtension
  CondensedRing.openImmersionLowerShriekUpperStarAdjunction Subobject.ofLE Subobject.mk
  CondensedRing.openImmersionLowerShriek CondensedRing.lowerStar
  _root_.DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency true in
/-- Constructible sheaves over E or Qbar_l form an essentially small abelian heart, with
finite locally closed lisse filtrations and the stated curve localization sequence.
The Noetherian structure used to state the assertion is constructed from the standing
finite-type-over-a-field hypotheses, rather than imposed as an additional assumption.

Source: blueprint lemma-constructible-sheaves and its proof, all ten steps
(blueprint: lemma-constructible-sheaves).

Proof plan:
1. The standing finite-type scheme is Noetherian (lemma-constructible-sheaves--7).
Its open, closed and locally closed subschemes are Noetherian, all opens quasi-compact,
and X quasi-separated. Identify the actual condensed coefficients using
lemma-comparison-completed-coefficients; these are not discrete constant field sheaves.
2. The scalar ring is a field. A finite constant presentation is therefore finite free,
and conversely. This gives the finite-stratification lisse criterion. The field case of
lemma-constructible-sheaves--7 gives Dctf = Dbc. Truncation only removes cohomology
sheaves or replaces them by zero, so preserves bounded constructibility.
3. Factor an immersion through its scheme-theoretic image using
lemma-schematic-closure-uniqueness--1. Restriction to an open in which it is closed identifies this
image with S; thus the map to its image is open (lemma-nagata-scheme-image-restrict-open
and -of-closed-immersion). Use prose-03-02 and lemma-constructible-sheaves--7 for exactness
of both factors. Their composite preserves quasi-isomorphisms and induces the localization
functor with the displayed termwise comparison, without resolutions.
4. Use lemma-constructible-sheaves for a common adapted stratification
and exact restriction. On each stratum kernels and cokernels are lisse by
lemma-constructible-sheaves, so the criterion in step 2 makes them constructible.
5. Restrict an extension to the same common stratification. Locally lift finitely many basis
sections of its free quotient to split it. Its middle term is finite free. Thus extensions
are constructible. Zero has rank zero; split extensions give finite sums. The ambient kernels
and cokernels now give an abelian full subcategory and exact inclusion, as in the closure node.
6. lemma-constructible-sheaves--6 supplies a set of representatives, including the control
of gluing between strata by embeddings into the product of stratum direct images.
7. Order and refine an adapted stratification by lemma-constructible-sheaves.
Apply lemma-constructible-sheaves--7 to its open prefixes: their counit image subobjects
start at zero and end at F, are nested, and their quotients are the specified a_! of the
lisse restrictions. Equality between successive subobjects is permitted, including F = 0.
8. On a curve choose a generic point of each of its finitely many irreducible components
(lemma-constructible-sheaves--7, lemma-constructible-sheaves--7). Its adapted stratum
contains a neighborhood after other components are removed. Base change this neighborhood
with that stratum. The projection is a surjective immersion, hence closed; this follows from
lemma-constructible-sheaves--7 and lemma-constructible-sheaves--7. The other projection
is open, so the pulled-back sheaf is lisse. No factorization through a nonreduced stratum is
inferred just from containment of underlying point sets.
9. Lift the trivializing cover through this surjective closed immersion by
new-lem-weil-pbc-proetale-surjective-closed-cover-refinement. Each base change is a universal
homeomorphism (lemma-constructible-sheaves--7), and its
coefficient pullback is an equivalence (new-lem-weil-pbc-condensed-surjective-closed-equivalence).
Cartesian coefficients identify free modules. Fullness lifts a trivialization and its inverse;
faithfulness gives their inverse identities. These neighborhoods give a dense lisse open U.
10. Give its complement the reduced induced closed scheme structure
(lemma-constructible-sheaves--7). It misses every component's generic point,
so a chain of length one in the complement would give length two in X. The complement has
dimension at most zero, is Noetherian and T0, hence consists of finitely many closed points
(lemma-constructible-sheaves--7). Apply lemma-constructible-sheaves--7 with
lemma-inverse-image-coefficient-sheaves. Its actual counit and unit give the short exact sequence;
open restriction of the closed term is zero, giving its support. The argument allows
reducible and nonreduced curves, the empty complement, the zero sheaf and empty X. -/
theorem coefficientHeart (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    @CoefficientHeartAssertions (coefficientHeartRingObj L) _ _ X
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) } := by
  classical
  have _characteristic_separation := hpℓ
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have hcoeff :
      Nonempty (Mon.mk (coefficientHeartRingObj L) ≅
        Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk (coefficientHeartRingObj L) ≅
        Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk (coefficientHeartRingObj L) ≅
          Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk (coefficientHeartRingObj L) ≅
        Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk (coefficientHeartRingObj L) ≅
        Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hL with ⟨E, hE, hL⟩ | hL
    · refine Or.inr (Or.inr (Or.inl ⟨⟨E, hE⟩, Or.inr ⟨?_⟩⟩))
      exact eqToIso (congrArg (fun R ↦ Mon.mk (coefficientHeartRingObj R)) hL)
    · refine Or.inr (Or.inr (Or.inr ⟨?_⟩))
      exact eqToIso (congrArg (fun R ↦ Mon.mk (coefficientHeartRingObj R)) hL)
  have htor := (localizingClosure_ctf_equals_bc ℓ X (coefficientHeartRingObj L) hcoeff).1.2.2.1
  have hclosure := (coefficientHeart_closure ℓ L hL).2 X
  have hk := hclosure.1
  have hc := hclosure.2.1
  have he := hclosure.2.2.1
  have hab := hclosure.2.2.2.1
  have hlim := hclosure.2.2.2.2.1
  have hcolim := hclosure.2.2.2.2.2.1
  have hstrata := hclosure.2.2.2.2.2.2
  let P : ObjectProperty _ := IsConstantModelConstructible (coefficientHeartRingObj L) X
  have : P.IsClosedUnderKernels := hk
  have : P.IsClosedUnderCokernels := hc
  have : P.IsClosedUnderExtensions := he
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (coefficientHeartRingObj L) X).1
  have : P.ContainsZero := by
    have : Abelian P.FullSubcategory := hab.some
    have : PreservesFiniteLimits P.ι := hlim
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := P.FullSubcategory)
    exact ⟨⟨Z.obj, P.ι.map_isZero hZ, Z.property⟩⟩
  refine ⟨htor, ?_, hstrata, ?_, ?_, ?_, hab, hlim, hcolim,
    coefficientHeart_essentiallySmall ℓ L hL X, ?_, ?_⟩
  · intro K n hK
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hcoh⟩ := hK
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncLE hcoh n⟩,
      ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncGE hcoh n⟩⟩
  · intro S a ha
    obtain ⟨hu, h⟩ :=
      ((coefficientHeart_locallyClosedExtension (coefficientHeartRingObj L) X).2 S a ha).2.2.2.2.2
    obtain ⟨hadd, hD⟩ := h.2.2.2.2.2.2
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      hadd, hD.2.2⟩
  · intro F G f
    exact ⟨P.prop_kernel f F.property G.property, P.prop_cokernel f F.property G.property⟩
  · intro F G M f g hf hg hex
    have := hf
    have := hg
    let Q := ShortComplex.mk f g (hex.zero 0)
    have hQ : Q.Exact := Q.exact_iff_exact_toComposableArrows.mpr hex
    exact P.prop_X₂_of_shortExact (S := Q) (ShortComplex.ShortExact.mk' hQ hf hg)
      F.property G.property
  · intro F
    obtain ⟨S, hS⟩ := (hstrata F.obj).mp F.property
    have hcommon := coefficientHeart_commonStratification ℓ L X hL
    obtain ⟨R, hRall⟩ := hcommon.1 1 (fun _ ↦ S)
    have hR := hRall.1
    have hopen := hRall.2.2
    have hRfree := hcommon.2.1.2 S R F.obj
      (fun a ↦ heart_free_model (coefficientHeartRingObj L) _ (hS a)) (hR 0)
    let V (a : Fin (R.n + 1)) : X.Opens := ⟨_, hopen a⟩
    have hfil := coefficientHeart_filtration ℓ L hL X F.obj
      F.property R (fun a ↦ heart_free_model (coefficientHeartRingObj L) _ (hRfree a))
      V (fun _ ↦ rfl)
    simp only [← heartFiltrationImage_eq] at hfil
    obtain ⟨h, hquot⟩ := hfil.2.2.2
    refine ⟨R.n, fun a ↦ heartFiltrationImage (coefficientHeartRingObj L) F.obj (V a),
      hfil.2.1, hfil.2.2.1,
      h, fun a ↦ ?_⟩
    refine ⟨R.domain a, R.immersion a, R.isImmersion a,
      (CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F.obj, ?_, ?_⟩
    · exact (hquot a).2
    · have hq := (hquot a).1
      exact hq
  · intro hdim F
    obtain ⟨S, hS⟩ := (hstrata F.obj).mp F.property
    have hn := (X.exists_stratification_generic_neighborhoods S).2
    obtain ⟨η, j, W, hn⟩ := hn
    have hW := hn.1
    have hdense := hn.2.1
    have hgeneric := hn.2.2
    have hlocal (C : irreducibleComponents X) :
        IsLisseCoefficientModule (coefficientHeartRingObj L)
          ((CondensedRing.upperStar (coefficientHeartRingObj L) (W C).ι).obj F.obj) := by
      have : Surjective (pullback.fst (W C).ι (S.immersion (j C))) := (hW C).2.2.2.2.2.2.1
      have : IsClosedImmersion (pullback.fst (W C).ι (S.immersion (j C))) := (hW C).2.2.2.2.2.2.2.1
      exact heartLisse_closed_square_coefficient L (W C).ι (S.immersion (j C))
        (pullback.fst (W C).ι (S.immersion (j C)))
        (pullback.snd (W C).ι (S.immersion (j C))) pullback.condition F.obj (hS (j C))
    have hlisse := heartLisse_iSup_coefficient L W F.obj hlocal
    have hgen : ∀ C ∈ irreducibleComponents X, ∀ x : X,
        IsGenericPoint x C → x ∈ (⨆ C, W C : X.Opens) := by
      intro C hC x hx
      rw [(hW ⟨C, hC⟩).2.1 x hx]
      exact hgeneric ⟨C, hC⟩
    have hZ : ∃ Z : Scheme.{u}, ∃ i : Z ⟶ X,
        IsClosedImmersion i ∧ IsReduced Z ∧
          Set.range i = ((⨆ C, W C : X.Opens) : Set X)ᶜ := by
      exact ⟨heartComplement (⨆ C, W C), heartComplementι (⨆ C, W C),
        inferInstance, inferInstance, heartComplement_range _⟩
    obtain ⟨Z, i, hiClosed, hiReduced, hi⟩ := hZ
    have := hiClosed
    have := hiReduced
    have hcomp := coefficientHeart_curve_complement (coefficientHeartRingObj L)
      X hdim (⨆ C, W C : X.Opens) hgen Z i hi F.obj
    have : Finite Z := hcomp.2.1
    refine ⟨(⨆ C, W C : X.Opens), hdense, hlisse, Z, i, hiClosed, hi,
      ?_, ?_, hcomp.2.2.2⟩
    · rw [← hi]
      exact Set.finite_range _
    · intro x hx
      obtain ⟨z, rfl⟩ := hi.symm ▸ hx
      exact hcomp.2.2.1 z

end AlgebraicGeometry.ProEtale
