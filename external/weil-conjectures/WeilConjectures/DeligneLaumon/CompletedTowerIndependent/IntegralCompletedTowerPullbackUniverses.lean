/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives
import
  WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.CochainCompositeConstruction.CochainCompositeAlgebraic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
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
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import WeilConjectures.Algebra.Homology.RingedSiteKFlatStalkCriterion
import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.RingedSitePointUniversalTensor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.Algebra.Homology.RingedSitePointTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.PUnit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Homology.RingedSitePointExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.RingedSitePointFinitePresentationRetract
import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.Sites.InverseImageFreeModule
import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import WeilConjectures.CategoryTheory.Sites.NormalizedFreeModuleComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Finsupp.Pi
import WeilConjectures.Algebra.Homology.RingedSitePointKFlatResolution
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.RingedSitePointAcyclic
import WeilConjectures.Algebra.Homology.UniversalAcyclicModuleKFlat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.Algebra.ModuleDirectedColimitFinitePresentation
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.ProEtaleEnoughPoints
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.Sites.FinitarySliceEnoughPoints
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.FinitarySiteEnoughPoints
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.CategoryTheory.Sites.PointSystemSaturation
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.PointSystemRefineAll
import WeilConjectures.CategoryTheory.PointSystemRefinementMap
import WeilConjectures.AlgebraicGeometry.PointSystemRefine
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.PointSystemRefinementChainExists
import WeilConjectures.CategoryTheory.PointSystemChain
import Mathlib.Order.Directed
import WeilConjectures.CategoryTheory.PointSystemExtensions
import WeilConjectures.CategoryTheory.PointSystemDiagram
import Mathlib.Order.Category.PartOrdEmb
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Order.Hom.Set
import WeilConjectures.CategoryTheory.PointSystemPosetalRefine
import WeilConjectures.CategoryTheory.PointSystemPosetalReplacement
import Mathlib.Order.Antisymmetrization
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.PointSystemSchedule
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.CategoryTheory.Filtered.Grothendieck
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Sites.PointFamilyConservative
import WeilConjectures.TraceFormula.InverseSystemSitePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import all WeilConjectures.CategoryTheory.RingedToposMorphism.RingedToposDerivedAdjunctionOfUniverses
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientStructureMap
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Integral completed strict-tower interfaces at independent universes

Source: Stacks Project, Tags 099N(5), 03D2, 03D3, 06YS, 06YY and 06XN
(blueprint: def-a1-integral-completed-tower-pullback-universes).
This is the O_E specialization at independent scheme and coefficient sizes.
It retains the actual completed sheaf and quotient transitions on the small site.
It does not replace the general adic datum or the Rlim completed-pullback interface.

## Main definitions

* `reductionPair` is strict derived reduction with its universal computation counit.
* `directRingMap` is the adjoint completed structural map fixed by all projections.
* `pull` is its ordinary ringed module pullback, fixed by its adjunction unit.
* `derivedPull` is the universal derived pullback of strict towers, before Rlim.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxErrors 4
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace IndependentSite

-- Restrict a set-level adjunction to the faithful categories of linear maps.
-- Adapted from VaryingRingTensorComparison.restrictedAdjunction (Stacks 03D7).
section RestrictedAdjunction
universe c₁ v₁ c₂ v₂ c₃ v₃ c₄ v₄ c₅ v₅
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restrictedAdjunction
    {C : Type c₁} {D : Type c₂} {E : Type c₃} {A : Type c₄} {B : Type c₅}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    [Category.{v₄} A] [Category.{v₅} B]
    (I : C ⥤ E) (T : D ⥤ E) (Q : E ⥤ D) (q : Q ⊣ T) (P : D ⥤ C)
    (U : C ⥤ A) [U.Faithful] (W : E ⥤ B)
    (L : A ⥤ B) (V : B ⥤ A) (a : L ⊣ V)
    (eI : I ⋙ W ≅ U ⋙ L) (eP : P ⋙ U ≅ T ⋙ W ⋙ V)
    (E' : ∀ M H, (I.obj M ⟶ T.obj H) ≃ (M ⟶ P.obj H))
    (hE : ∀ M H f, U.map (E' M H f) ≫ eP.hom.app H =
      a.homEquiv _ _ (eI.inv.app M ≫ W.map f)) :
    ∃ am : I ⋙ Q ⊣ P, ∀ M H f,
      U.map (am.homEquiv M H f) ≫ eP.hom.app H =
        a.homEquiv _ _ (eI.inv.app M ≫ W.map (q.homEquiv _ _ f)) := by
  have hleft {M N : C} (b : M ⟶ N) (H : D) (f : I.obj N ⟶ T.obj H) :
      E' M H (I.map b ≫ f) = b ≫ E' N H f := by
    apply U.map_injective
    apply (cancel_mono (eP.hom.app H)).mp
    rw [hE, U.map_comp, Category.assoc, hE, W.map_comp]
    have hn : eI.inv.app M ≫ W.map (I.map b) =
        L.map (U.map b) ≫ eI.inv.app N := (eI.inv.naturality b).symm
    rw [← Category.assoc, hn, Category.assoc, a.homEquiv_naturality_left]
  have hright (M : C) {H H' : D} (f : I.obj M ⟶ T.obj H) (b : H ⟶ H') :
      E' M H' (f ≫ T.map b) = E' M H f ≫ P.map b := by
    apply U.map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    have hp : U.map (P.map b) ≫ eP.hom.app H' =
        eP.hom.app H ≫ V.map (W.map (T.map b)) := eP.hom.naturality b
    rw [hE, U.map_comp, Category.assoc, hp, ← Category.assoc,
      hE, W.map_comp, ← Category.assoc, a.homEquiv_naturality_right]
  let equiv : ∀ M H, ((I ⋙ Q).obj M ⟶ H) ≃ (M ⟶ P.obj H) :=
    fun M H ↦ (q.homEquiv _ _).trans (E' M H)
  have hn {M N : C} (b : M ⟶ N) (H : D) (f : (I ⋙ Q).obj N ⟶ H) :
      equiv M H ((I ⋙ Q).map b ≫ f) = b ≫ equiv N H f := by
    dsimp only [equiv, Equiv.trans_apply, Functor.comp_map]
    rw [q.homEquiv_naturality_left, hleft]
  let am : I ⋙ Q ⊣ P := Adjunction.mkOfHomEquiv {
    homEquiv := equiv
    homEquiv_naturality_left_symm := by
      intro M N H b f
      apply (equiv M H).injective
      rw [Equiv.apply_symm_apply, hn, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M H H' f b
      dsimp only [equiv, Equiv.trans_apply]
      rw [q.homEquiv_naturality_right, hright] }
  refine ⟨am, ?_⟩
  intro M H f
  dsimp only [am]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact hE M H _
end RestrictedAdjunction
universe v w
open MonoidalCategory SheafOfModules
open SheafOfModules.GeometricConstruction
open scoped ChangeOfRings
attribute [local irreducible] SheafOfModules.monoidalCategory
private abbrev Mod {C : Type (v + 1)} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) :=
  SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w}
      RingCat.{w})).obj R)
set_option backward.defeqAttrib.useBackward true

private instance siteBinaryProducts {C : Type (v + 1)} [Category.{v} C]
    {J : GrothendieckTopology C} :
    HasBinaryProducts (Sheaf J (Type (w))) := by
  infer_instance

private instance siteProduct {C : Type (v + 1)} [Category.{v} C]
    {J : GrothendieckTopology C} (X Y : Sheaf J (Type w)) :
    HasBinaryProduct X Y := by infer_instance

section
variable {C : Type (v + 1)} {D : Type (v + 1)} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (F : D ⥤ C) [F.IsContinuous K J]
  (L : Sheaf K (Type (w)) ⥤ Sheaf J (Type (w)))
  (adj : L ⊣ F.sheafPushforwardContinuous (Type (w)) K J)

private def directPair {X Y : Sheaf J (Type (w))}
    {T : Sheaf K (Type (w))}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj Y) :
    T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj (X ⊗ Y) :=
  ⟨{ app U := ↾(fun t ↦ (x.hom.app U t, y.hom.app U t))
     naturality := by
       intro U V f
       ext t
       change (x.hom.app V (T.obj.map f t), y.hom.app V (T.obj.map f t)) =
         (X.obj.map (F.op.map f) (x.hom.app U t),
           Y.obj.map (F.op.map f) (y.hom.app U t))
       exact Prod.ext (CategoryTheory.congr_fun (x.hom.naturality f) t)
         (CategoryTheory.congr_fun (y.hom.naturality f) t) }⟩

omit [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
private theorem transpose_pair {X Y : Sheaf J (Type (w))}
    {T : Sheaf K (Type (w))}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj Y) :
    (adj.homEquiv T (X ⊗ Y)).symm (directPair F x y) =
      CartesianMonoidalCategory.lift ((adj.homEquiv T X).symm x)
        ((adj.homEquiv T Y).symm y) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst, ← adj.homEquiv_naturality_right_symm]
    rfl
  · rw [CartesianMonoidalCategory.lift_snd, ← adj.homEquiv_naturality_right_symm]
    rfl

omit [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
private theorem transpose_binary
    {X Y Z : Sheaf J (Type (w))} {T : Sheaf K (Type (w))} (op : X ⊗ Y ⟶ Z)
    (x : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj Y)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj Z)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U)
      (x.hom.app U t, y.hom.app U t)) :
    ∀ U t, ((adj.homEquiv T Z).symm z).hom.app U t =
      op.hom.app U (((adj.homEquiv T X).symm x).hom.app U t,
        ((adj.homEquiv T Y).symm y).hom.app U t) := by
  have he : z = directPair F x y ≫
      (F.sheafPushforwardContinuous (Type (w)) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm, transpose_pair F L adj]
  intro U t
  rfl

omit [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
private theorem transpose_constant
    {X : Sheaf J (Type (w))} {T : Sheaf K (Type (w))}
    (op : 𝟙_ (Sheaf J (Type (w))) ⟶ X)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj X)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U) PUnit.unit) :
    ∀ U t, ((adj.homEquiv T X).symm z).hom.app U t = op.hom.app U PUnit.unit := by
  let w : T ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj (𝟙_ _) :=
    ⟨{ app U := ↾(fun _ ↦ PUnit.unit) }⟩
  have he : z = w ≫ (F.sheafPushforwardContinuous (Type (w)) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm]
  intro U t
  change op.hom.app U _ = _
  congr 1

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
private theorem siteStructuralMap_exists
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
    (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} K J).obj R)
    (RI : Sheaf J CommRingCat.{w}) (I : AlgebraicInverseImage L S RI) :
    ∃ c : RI ⟶ R, (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset S) (rset R)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map φ) := by
  let φs : rset S ⟶ (F.sheafPushforwardContinuous (Type (w)) K J).obj (rset R) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map φ
  let g := (adj.homEquiv (rset S) (rset R)).symm φs
  refine SheafOfModules.CochainCompositeConstruction.structuralMap L S R RI I g ?_ ?_ ?_
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Add.add (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (ringAdd R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') + (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') + (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_add _ _)
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Mul.mul (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (ringMul R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') * (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') * (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_mul _ _)
  · intro T z hz U t
    change T ⟶ rset S at z
    change ((L.map z) ≫ g).hom.app U t = (1 : R.obj.obj U)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm]
    apply transpose_constant F L adj (ringOne R) (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 1
    have h : (show S.obj.obj V from z.hom.app V x) = 1 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_one

end
private noncomputable def tensorFunctor
    {D : Type (v + 1)} [Category.{v} D] [EssentiallySmall.{w} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) :=
  CategoryTheory.CochainPullback.extensionFunctor (J := K) (A := A) (B := S) c

private noncomputable def tensorAdjunction
    {D : Type (v + 1)} [Category.{v} D] [EssentiallySmall.{w} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) :
    tensorFunctor c ⊣ restrictScalars
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map c) :=
  CategoryTheory.CochainPullback.extensionAdjunction (J := K) (A := A) (B := S) c

attribute [local irreducible] tensorFunctor tensorAdjunction

open SheafOfModules.GeometricConstruction
attribute [local irreducible] SheafOfModules.GeometricConstruction.fromProd

private theorem module_add_apply
    {C : Type (v + 1)} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) (M : Mod R) (U : Cᵒᵖ)
    (p : (((mset R).obj M) ⨯ ((mset R).obj M)).obj.obj U) :
    (CategoryTheory.CochainPullback.moduleAddMap R M).hom.app U p =
      @Add.add (M.val.obj U) inferInstance
        ((prod.fst : (mset R).obj M ⨯ (mset R).obj M ⟶ _).hom.app U p)
        ((prod.snd : (mset R).obj M ⨯ (mset R).obj M ⟶ _).hom.app U p) := by
  let X := (mset R).obj M
  have hf := congrArg (fun f ↦ f.hom.app U p) (fromProd_fst X X)
  have hs := congrArg (fun f ↦ f.hom.app U p) (fromProd_snd X X)
  change ((fromProd X X).hom.app U p).1 = _ at hf
  change ((fromProd X X).hom.app U p).2 = _ at hs
  change @Add.add (M.val.obj U) inferInstance
    ((fromProd X X).hom.app U p).1 ((fromProd X X).hom.app U p).2 = _
  rw [hf, hs]

private theorem module_smul_apply
    {C : Type (v + 1)} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) (M : Mod R) (U : Cᵒᵖ)
    (p : (rset R ⨯ (mset R).obj M).obj.obj U) :
    (CategoryTheory.CochainPullback.moduleSMulMap R M).hom.app U p =
      @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance
        ((prod.fst : rset R ⨯ (mset R).obj M ⟶ _).hom.app U p)
        ((prod.snd : rset R ⨯ (mset R).obj M ⟶ _).hom.app U p) := by
  let X := (mset R).obj M
  have hf := congrArg (fun f ↦ f.hom.app U p) (fromProd_fst (rset R) X)
  have hs := congrArg (fun f ↦ f.hom.app U p) (fromProd_snd (rset R) X)
  change ((fromProd (rset R) X).hom.app U p).1 = _ at hf
  change ((fromProd (rset R) X).hom.app U p).2 = _ at hs
  change @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance
    ((fromProd (rset R) X).hom.app U p).1 ((fromProd (rset R) X).hom.app U p).2 = _
  exact congrArg₂ (fun a x ↦ @SMul.smul (R.obj.obj U) (M.val.obj U)
    inferInstance a x) hf hs

private theorem pushforward_operations
    {C : Type (v + 1)} {D : Type (v + 1)} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (F : D ⥤ C) [F.IsContinuous K J]
    (A : Sheaf J CommRingCat.{w}) (B : Sheaf K CommRingCat.{w})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} K J).obj A)
    (H : Mod A) :
    let V := F.sheafPushforwardContinuous (Type (w)) K J
    let P := SheafOfModules.pushforward.{w} (F := F)
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
    let X := (mset A).obj H
    V.map (CategoryTheory.CochainPullback.moduleAddMap A H) =
      prodComparison V X X ≫ CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) := by
  dsimp only
  let V := F.sheafPushforwardContinuous (Type (w)) K J
  let X := (mset A).obj H
  ext U p
  let : Add (X.obj.obj (F.op.obj U)) :=
    (inferInstance : Add (H.val.obj (F.op.obj U)))
  let : Add ((V.obj X).obj.obj U) :=
    (inferInstance : Add (H.val.obj (F.op.obj U)))
  have hf := congrArg (fun f ↦ f.hom.app U p) (prodComparison_fst V X X)
  have hs := congrArg (fun f ↦ f.hom.app U p) (prodComparison_snd V X X)
  change (CategoryTheory.CochainPullback.moduleAddMap A H).hom.app
      (F.op.obj U) p =
    (CategoryTheory.CochainPullback.moduleAddMap B
      ((SheafOfModules.pushforward ((sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj H)).hom.app U
      ((prodComparison V X X).hom.app U p)
  rw [module_add_apply, module_add_apply]
  exact congrArg₂ (fun x y ↦ x + y) hf.symm hs.symm

private theorem pushforward_action
    {C : Type (v + 1)} {D : Type (v + 1)} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (F : D ⥤ C) [F.IsContinuous K J]
    [PreservesFiniteLimits (F.sheafPushforwardContinuous (Type (w)) K J)]
    (A : Sheaf J CommRingCat.{w}) (B : Sheaf K CommRingCat.{w})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} K J).obj A)
    (H : Mod A) :
    let V := F.sheafPushforwardContinuous (Type (w)) K J
    let P := SheafOfModules.pushforward.{w} (F := F)
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
    let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map φ
    let X := (mset A).obj H
    CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) =
      prod.map φs (𝟙 (V.obj X)) ≫ inv (prodComparison V (rset A) X) ≫
        V.map (CategoryTheory.CochainPullback.moduleSMulMap A H) := by
  dsimp only
  let V := F.sheafPushforwardContinuous (Type (w)) K J
  let X := (mset A).obj H
  let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map φ
  ext U p
  let q := (prod.map φs (𝟙 (V.obj X)) ≫ inv (prodComparison V (rset A) X)).hom.app U p
  have hf := congrArg (fun f ↦ f.hom.app U p)
    (show prod.map φs (𝟙 (V.obj X)) ≫ inv (prodComparison V (rset A) X) ≫
        V.map (prod.fst : rset A ⨯ X ⟶ rset A) =
      (prod.fst : rset B ⨯ V.obj X ⟶ rset B) ≫ φs by
      rw [inv_prodComparison_map_fst, prod.map_fst])
  have hs := congrArg (fun f ↦ f.hom.app U p)
    (show prod.map φs (𝟙 (V.obj X)) ≫ inv (prodComparison V (rset A) X) ≫
        V.map (prod.snd : rset A ⨯ X ⟶ X) =
      (prod.snd : rset B ⨯ V.obj X ⟶ V.obj X) by
      rw [inv_prodComparison_map_snd, prod.map_snd, Category.comp_id])
  let smul : A.obj.obj (F.op.obj U) → H.val.obj (F.op.obj U) →
      H.val.obj (F.op.obj U) := fun a x ↦ a • x
  change (CategoryTheory.CochainPullback.moduleSMulMap B
      ((SheafOfModules.pushforward ((sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj H)).hom.app U p =
    (CategoryTheory.CochainPullback.moduleSMulMap A H).hom.app (F.op.obj U) q
  let P := SheafOfModules.pushforward.{w} (F := F) (J := K) (K := J)
    (R := base A) (S := base B) ((sheafCompose K
    (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  exact (module_smul_apply B (P.obj H) U p).trans
    ((congrArg₂ smul hf.symm hs.symm).trans
      (module_smul_apply A H (F.op.obj U) q).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Elaborate the sectionwise adjunction and its transported coefficient identities.
-- Restricting the adjunction to linear maps elaborates several large sheaf diagrams.
private theorem supplied_adjunction
    {C : Type (v + 1)} {D : Type (v + 1)} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type (w)) ⥤ Sheaf J (Type (w)))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (w)) K J)
    [PreservesFiniteLimits L]
    (A : Sheaf J CommRingCat.{w}) (B : Sheaf K CommRingCat.{w})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} K J).obj A)
    (RI : Sheaf J CommRingCat.{w}) (I : AlgebraicInverseImage L B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset B) (rset A)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map φ)) :
    Nonempty (I.modules ⋙ tensorFunctor c ⊣
      SheafOfModules.pushforward.{w} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) := by
  let V := F.sheafPushforwardContinuous (Type (w)) K J
  let P := SheafOfModules.pushforward.{w} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map φ
  have : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let eI := I.moduleUnderlying
  obtain ⟨L₀, hobj₀, hmap₀, V₀, ⟨a₀⟩, hAdd₀⟩ :=
    CategoryTheory.CochainPullback.ringedPullbackPresentation_exists
      (R := B) (S := A) L V adj RI I c
  let p : CategoryTheory.CochainPullback.RingedPullback.{w, v + 1, v, v + 1, v}
      (J := K) (K := J) B A := {
    uInv := L, uPush := V, adj := adj, finiteLimits := inferInstance,
    RI := RI, I := I, coefficient := c, L := L₀, hobj := hobj₀, hmap := hmap₀,
    V := V₀, moduleAdj := a₀, additive := hAdd₀ }
  have hp : CategoryTheory.CochainPullback.structureMap p =
      (adj.homEquiv _ _).symm φs := by
    change I.ringUnderlying.hom ≫ _ = _
    rw [hc]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  have hEquiv (M : Mod B) (H : Mod A) :
      ∃ E : (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{w}
            RingCat.{w})).map c)).obj H) ≃ (M ⟶ P.obj H),
        ∀ a, (mset B).map (E a) =
          adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    have ha : CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) ≫ (𝟙 _) =
        prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
          V.map (CategoryTheory.CochainPullback.moduleAddMap A H) := by
      change CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) ≫ (𝟙 _) =
        prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V ((mset A).obj H)
          ((mset A).obj H)) ≫ V.map (CategoryTheory.CochainPullback.moduleAddMap A H)
      simp only [Category.comp_id, prod.map_id_id, Category.id_comp]
      apply (cancel_epi (prodComparison V ((mset A).obj H) ((mset A).obj H))).mp
      erw [IsIso.hom_inv_id_assoc]
      exact (pushforward_operations F A B φ H).symm
    have hs : CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) =
        prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) ((mset A).obj H)) ≫
          V.map (CategoryTheory.CochainPullback.moduleSMulMap A H) :=
      pushforward_action F A B φ H
    have hg : adj.homEquiv _ _ (CategoryTheory.CochainPullback.structureMap p) = φs := by
      rw [hp, Equiv.apply_symm_apply]
    rw [← hg] at hs
    obtain ⟨E, hE⟩ := CategoryTheory.CochainPullback.linearMate_exists p H (P.obj H)
      (Iso.refl _) ha (by
        simp only [Iso.refl_hom]
        change CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) = _
        exact hs) M
    refine ⟨E, fun a ↦ ?_⟩
    have h := hE a
    change (mset B).map (E a) ≫ (𝟙 _) =
      adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) at h
    exact (Category.comp_id _).symm.trans h
  let B' := fun M H ↦ (hEquiv M H).choose
  have hB := fun M H ↦ (hEquiv M H).choose_spec
  let restriction := restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{w} RingCat.{w})).map c)
  let eP : P ⋙ mset B ≅ restriction ⋙ mset RI ⋙ V :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  obtain ⟨am, _⟩ := restrictedAdjunction
    I.modules restriction (tensorFunctor c) (tensorAdjunction c) P
    (mset B) (mset RI) L V adj eI eP B' (by
      intro M H a
      change (mset B).map (B' M H a) ≫ (𝟙 _) = _
      exact (Category.comp_id _).trans (hB M H a))
  exact ⟨am⟩

end IndependentSite

-- Keep localization independent of the concrete completed coefficient categories.
private theorem deriveFromFunctorialResolution
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {D : Type*} [Category* D]
    (P : ObjectProperty (CochainComplex A ℤ)) (H : CochainComplex A ℤ ⥤ D)
    (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ) (η : F ⟶ 𝟭 _)
    (hgood : ∀ K, P (F.obj K)) (hη : ∀ K, QuasiIso (η.app K))
    (hinverts : ∀ {K L} (f : K ⟶ L), P K → P L → QuasiIso f → IsIso (H.map f)) :
    ∃ (L : DerivedCategory A ⥤ D) (ε : DerivedCategory.Q ⋙ L ⟶ H),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      ∀ K, P K → IsIso (ε.app K) := by
  let Q := HomologicalComplex.quasiIso A (.up ℤ)
  let Φ : LocalizerMorphism (Q.inverseImage P.ι) Q :=
    ⟨P.ι, fun _ _ _ hf ↦ hf⟩
  let ρ := P.lift F hgood
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLeftDerivabilityStructure :=
    Φ.isLeftDerivabilityStructure_of_functorial_resolutions
      (ρ := ρ) η hη rfl
  have hderives : Φ.Derives H := by
    intro K L f h
    exact hinverts f.hom K.property L.property h
  have : H.HasLeftDerivedFunctor Q := hderives.hasLeftDerivedFunctor
  let L := H.totalLeftDerived DerivedCategory.Q Q
  let ε := H.totalLeftDerivedCounit DerivedCategory.Q Q
  refine ⟨L, ε, inferInstance, ?_⟩
  intro K hK
  exact hderives.isIso_of_isLeftDerivedFunctor ε ⟨K, hK⟩

-- The resolving-class argument is independent of the completed coefficient construction.
private theorem deriveOfComplexResolutions
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (G : A ⥤ B) [G.Additive] (good : CochainComplex A ℤ → Prop)
    (resolves : ∀ P : CochainComplex A ℤ,
      ∃ (L : CochainComplex A ℤ) (a : L ⟶ P), good L ∧ QuasiIso a)
    (hpres : ∀ {P Q : CochainComplex A ℤ} (a : P ⟶ Q), good P → good Q →
      QuasiIso a → QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map a)) :
    ∃ (V : DerivedCategory A ⥤ DerivedCategory B)
      (ε : DerivedCategory.Q ⋙ V ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      V.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (∃ (_ : V.CommShift ℤ), V.IsTriangulated) ∧
      ∀ P : CochainComplex A ℤ, good P → IsIso (ε.app P) := by
  classical
  let T := G.mapHomologicalComplex (.up ℤ)
  let H := HomotopyCategory.quotient A (.up ℤ)
  let F := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let K : Set (HomotopyCategory A (.up ℤ)) :=
    {P | ∃ L : CochainComplex A ℤ, H.obj L = P ∧ good L}
  have hres (P : HomotopyCategory A (.up ℤ)) :
      ∃ (L : HomotopyCategory A (.up ℤ)) (a : L ⟶ P),
        L ∈ K ∧ HomotopyCategory.quasiIso A (.up ℤ) a := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    obtain ⟨L, a, hL, ha⟩ := resolves P
    exact ⟨H.obj L, H.map a, ⟨L, rfl, hL⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff a).2 ha⟩
  have hinv (P Q : HomotopyCategory A (.up ℤ)) (a : P ⟶ Q)
      (hp : P ∈ K) (hq : Q ∈ K) (ha : HomotopyCategory.quasiIso A (.up ℤ) a) :
      IsIso (F.map a) := by
    obtain ⟨P, rfl, hp⟩ := hp
    obtain ⟨Q, rfl, hq⟩ := hq
    obtain ⟨a, rfl⟩ := H.map_surjective a
    have ht := hpres a hp hq ((HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 ha)
    change IsIso (DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map (H.map a)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff (T.map a)).2 ht)
  obtain ⟨_, LF, ε, hu, ht, hc⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F K hres hinv
  have := hu
  obtain ⟨εc, hεc, heq⟩ := CategoryTheory.leftDerivedOnComplexes
    G (𝟭 (DerivedCategory B)) LF ε
  refine ⟨LF, εc, hεc, ht, ?_⟩
  intro P hP
  rw [heq]
  exact hc (H.obj P) ⟨P, rfl, hP⟩

namespace WeilConjectures.CompletedTowerIndependent
attribute [local irreducible] HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded completed module category, at its actual coefficient size.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
abbrev Modules (W : Scheme.{t}) := SheafOfModules.{max u (t + 1)}
  (completedIntegralCoefficientSheafUnrestricted l E W)

/-- Strict inverse sequences of completed modules.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
abbrev Towers (W : Scheme.{t}) := ℕᵒᵖ ⥤ Modules l E W

/-- The standard localization of the strict tower category.
Source: Stacks 05RU (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
instance towerDerived (W : Scheme.{t}) : HasDerivedCategory (Towers l E W) :=
  HasDerivedCategory.standard _

/-- Transposition of the existing strict diagrams, with every transition retained.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def transpose (W : Scheme.{t}) : (ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ) ⥤
    CochainComplex (Towers l E W) ℤ :=
  PrincipalQuotientCompletion.transpose (completedIntegralCommRingSheafUnrestricted l E W)

/-- The canonical resolving-class pair, including its computation morphism.
Source: Stacks 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
structure DerivedPair (W Z : Scheme.{t})
    (F : CochainComplex (Modules l E W) ℤ ⥤ CochainComplex (Towers l E Z) ℤ) where
  functor : DerivedCategory (Modules l E W) ⥤ DerivedCategory (Towers l E Z)
  counit : DerivedCategory.Q ⋙ functor ⟶ F ⋙ DerivedCategory.Q
  universal : functor.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (Modules l E W) (.up ℤ))
  computes : ∀ P : CochainComplex (Modules l E W) ℤ,
    integralOperationsGoodComplex l E W P → IsIso (counit.app P)

/-- The existing actual quotient tower, transposed into a complex of strict towers.
Source: Stacks 06YY (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def reductionComplex (W : Scheme.{t}) : CochainComplex (Modules l E W) ℤ ⥤
    CochainComplex (Towers l E W) ℤ :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W)).flip ⋙ transpose l E W

/-- Reduction has the universal left-derived pair with its actual K-flat computation.
Source: Stacks 06YS, 06YY, 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: flat-term K-flat resolutions exist. Quotient tensoring preserves their
quasi-isomorphisms by change of rings. Exactness of towers is levelwise, so the
resolving-class theorem derives the whole strict construction with its counit. -/
theorem reduction_exists (W : Scheme.{t}) : Nonempty (DerivedPair l E W W
    (reductionComplex l E W)) := by
  classical
  let P := integralOperationsGoodComplex l E W
  let H := reductionComplex l E W ⋙ DerivedCategory.Q
  obtain ⟨F, η, hη, hk, hf⟩ := SheafOfModules.functorial_resolution
    (completedIntegralCommRingSheafUnrestricted l E W)
  have hinverts {K L : CochainComplex (Modules l E W) ℤ} (f : K ⟶ L)
      (hK : P K) (hL : P L) (h : QuasiIso f) : IsIso (H.map f) := by
    have hred : QuasiIso ((reductionComplex l E W).map f) := by
      apply (HomologicalComplex.quasiIso_iff_evaluation _).2
      intro n
      have hfinite := finiteReduction_quasiIso l E W n.unop f
        hK hL h
      let U := SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
          RingCat.{max u (t + 1)})).map
            (completedIntegralCommRingProjectionUnrestricted l E W n.unop))
      have hrest := coefficientRestriction_exact
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
          RingCat.{max u (t + 1)})).map
            (completedIntegralCommRingProjectionUnrestricted l E W n.unop))
      have : PreservesFiniteLimits U := hrest.1
      have : PreservesFiniteColimits U := hrest.2
      have : QuasiIso ((unrestrictedIntegralFiniteComplex l E W n.unop).map f) :=
        hfinite
      change QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map
        ((unrestrictedIntegralFiniteComplex l E W n.unop).map f))
      infer_instance
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (Towers l E W) (.up ℤ)) _ hred
  obtain ⟨L, ε, hu, hc⟩ := deriveFromFunctorialResolution P H F η
    (fun K ↦ ⟨hk K, hf K⟩) hη (fun f hK hL h ↦ hinverts f hK hL h)
  exact ⟨⟨L, ε, hu, hc⟩⟩

/-- The derived strict reduction, selected with its universal computation counit.
Source: Stacks 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def reductionPair (W : Scheme.{t}) : DerivedPair l E W W (reductionComplex l E W) :=
  Classical.choice (reduction_exists l E W)

end WeilConjectures.CompletedTowerIndependent

namespace WeilConjectures.CompletedTowerIndependent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Direct image of ring sheaves on the original small sites.
Source: Stacks 00VC (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
abbrev ringPush := (Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
  RingCat.{max u (t + 1)} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The finite component of the adjoint completed structural map.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def component (n : ℕ) : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
    (ringPush.{t, u} g).obj (integralCoefficientSheaf l E X n) :=
  limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
    (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (Scheme.coefficientProEtaleDirectRingMap g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

/-- The finite components commute with every quotient transition.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: the limit-cone equation identifies the two source projections, and the
constant-section direct-image map is natural in the coefficient quotient homomorphism.
Sheafification preserves this equality of constant-presheaf maps. -/
theorem component_naturality {a b : ℕᵒᵖ} (f : a ⟶ b) :
    component l E g a.unop ≫
        (ringPush.{t, u} g).map ((integralCoefficientSheafSystem l E X).map f) =
      component l E g b.unop := by
  obtain ⟨c, hc, _⟩ :=
    CompletedCoefficientPushforward.completedStructure_existsUnique (l := l) (E := E) g
  have hcomponent (n : ℕ) :
      c ≫ (ringPush.{t, u} g).map
        (limit.π (integralCoefficientSheafSystem l E X) (op n)) = component l E g n :=
    hc.1 n
  rw [← hcomponent a.unop, ← hcomponent b.unop, Category.assoc, ← Functor.map_comp]
  rw [limit.w]

/-- The adjoint of c_g, constructed by the target limit, rather than chosen arbitrarily.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def directRingMap : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
    (ringPush.{t, u} g).obj (completedIntegralCoefficientSheafUnrestricted l E X) :=
  (isLimitOfPreserves (ringPush.{t, u} g)
    (limit.isLimit (integralCoefficientSheafSystem l E X))).lift
      { pt := completedIntegralCoefficientSheafUnrestricted l E Y
        π := { app := fun n ↦ component l E g n.unop
               naturality := fun _a _b f ↦
                 (Category.id_comp _).trans (component_naturality l E g f).symm } }

/-- The sectionwise module direct image with the action through the structural map.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def push : Modules l E X ⥤ Modules l E Y :=
  SheafOfModules.pushforward (F := Scheme.proEtaleBaseChange g) (directRingMap l E g)

/-- The canonical ringed module pullback exists as the left adjoint to this pushforward.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: transport to the coefficient-sized AsSmall site model. Sheafify module Kan
extension along the transported directRingMap; its adjunction transports back to
exactly this pushforward on the original sites. This uniquely fixes G up to its unit. -/
@[instance] theorem push_isRightAdjoint : (push l E g).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (directRingMap l E g)

/-- Ordinary ringed module pullback G, fixed by its canonical adjunction.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def pull : Modules l E Y ⥤ Modules l E X := (push l E g).leftAdjoint

/-- The adjunction also fixes the inverse-image tensor generators.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def adjunction : pull l E g ⊣ push l E g := Adjunction.ofIsRightAdjoint _

/-- Ordinary pullback is additive; exactness is not asserted.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: sectionwise pushforward is additive, so its left adjoint is additive by the
preadditive adjunction criterion. -/
@[instance] theorem pull_additive : (pull l E g).Additive := by
  have : (push l E g).Additive := by
    constructor
    intro M N f h
    ext U x
    rfl
  exact (adjunction l E g).left_adjoint_additive

attribute [local irreducible] SheafOfModules.CochainCompositeConstruction.ringImage
  SheafOfModules.CochainCompositeConstruction.algebraicImage

set_option backward.isDefEq.respectTransparency.types true in
private theorem pull_quasiIso
    {P Q : CochainComplex (Modules l E Y) ℤ} (a : P ⟶ Q)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) Q)
    (ha : QuasiIso a) : QuasiIso (((pull l E g).mapHomologicalComplex (.up ℤ)).map a) := by
  classical
  let U := Scheme.proEtaleBaseChange g
  let J := Scheme.ProEt.topology Y
  let K := Scheme.ProEt.topology X
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let S := completedIntegralCommRingSheafUnrestricted l E X
  have : HasColimitsOfSize.{t, t + 1} (Type (max u (t + 1))) :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  let L := Functor.sheafPullbackConstruction.sheafPullback U
    (Type (max u (t + 1))) J K
  let V := U.sheafPushforwardContinuous (Type (max u (t + 1))) J K
  let adj : L ⊣ V := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (max u (t + 1))) J K
  have : AB5OfSize.{t, t + 1} (Type (max u (t + 1))) :=
    AB5OfSize_shrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : PreservesFiniteLimits (U.op.lan :
      (Y.ProEtᵒᵖ ⥤ Type (max u (t + 1))) ⥤ X.ProEtᵒᵖ ⥤ Type (max u (t + 1))) :=
    preservesFiniteLimits_op_lan_of_flat U
  have : PreservesFiniteLimits L := by
    dsimp only [L, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  have : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let RI := SheafOfModules.CochainCompositeConstruction.ringImage L R
  let I := SheafOfModules.CochainCompositeConstruction.algebraicImage L R
  let φ : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{max u (t + 1)} J K).obj S :=
    (sheafCompose J (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).preimage (directRingMap l E g)
  have hφ : (sheafCompose J (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map φ =
      directRingMap l E g :=
    Functor.map_preimage _ _
  obtain ⟨c, hc⟩ := IndependentSite.siteStructuralMap_exists U L adj S R φ RI I
  obtain ⟨am⟩ := IndependentSite.supplied_adjunction U L adj S R φ RI I c hc
  let T := I.modules ⋙ IndependentSite.tensorFunctor (K := K) (A := RI) (S := S) c
  have ham : T ⊣ push l E g := by
    change I.modules ⋙ IndependentSite.tensorFunctor (K := K) (A := RI) (S := S) c ⊣
      SheafOfModules.pushforward (directRingMap l E g)
    rw [← hφ]
    exact am
  have : T.Additive := by
    have : (push l E g).Additive := by
      constructor
      intro M N f h
      ext U x
      rfl
    exact ham.left_adjoint_additive
  have : PreservesFiniteLimits I.modules :=
    SheafOfModules.algebraicInverseImage_finiteLimits L I
  have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
  have : I.modules.PreservesEpimorphisms :=
    SheafOfModules.algebraicInverseImage_epi L V adj I
  have : I.modules.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels I.modules
  let geom : GeometricMorphism (Sheaf K (Type (max u (t + 1))))
      (Sheaf J (Type (max u (t + 1)))) :=
    { inverse := L, direct := V, adj := adj, leftExact := inferInstance }
  obtain ⟨ι, p, hpnt⟩ := AlgebraicGeometry.proEtale_enoughPoints.{t, u} X
  let s : ∀ i, CategoryTheory.RingedSitePoint RI (p i) :=
    fun i ↦ Classical.choice (CategoryTheory.RingedSitePoint.nonempty _ (p i))
  have hcons : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse) := by
    constructor
    intro A B f _
    exact hpnt f (fun i ↦ (isIso_iff_bijective ((p i).inverse.map f)).1 inferInstance)
  let IU := SheafOfModules.inverseImageOfUniverses_adapted I
  have : IU.modules.Additive := by
    change I.modules.Additive
    infer_instance
  have hk (Z : CochainComplex (Modules l E Y) ℤ)
      (hz : CochainComplex.IsKFlatIndependentCoefficients (R := R) Z) :
      CochainComplex.IsKFlatIndependentCoefficients
        ((I.modules.mapHomologicalComplex (.up ℤ)).obj Z) :=
    by
      have h := SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
        J K geom IU ι p s hcons Z hz
      change CochainComplex.IsKFlatIndependentCoefficients
        ((I.modules.mapHomologicalComplex (.up ℤ)).obj Z) at h
      exact h
  have : QuasiIso a := ha
  have : QuasiIso ((I.modules.mapHomologicalComplex (.up ℤ)).map a) := inferInstance
  have := SheafOfModules.scalarExtension_additive c
  have hscalar := SheafOfModules.scalarExtension_quasiIso c
    ((I.modules.mapHomologicalComplex (.up ℤ)).map a) (hk P hp) (hk Q hq)
    (by infer_instance)
  let e₀ : IndependentSite.tensorFunctor (K := K) (A := RI) (S := S) c ≅
      SheafOfModules.scalarExtension c := by
    unfold IndependentSite.tensorFunctor
    exact NatIso.ofComponents (fun M ↦ Iso.refl _) (by intro M N f; rfl)
  let e := (adjunction l E g).leftAdjointUniq ham ≪≫
    Functor.isoWhiskerLeft I.modules e₀
  let e' := NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl
      (I.modules ⋙ SheafOfModules.scalarExtension c)) (.up ℤ)).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e'.app P) (e'.app Q) (e'.hom.naturality a).symm)).2 hscalar

/-- Pullback of every object and transition of a strict tower.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def towerPull : Towers l E Y ⥤ Towers l E X :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pull l E g)

/-- The termwise additive structure on strict tower pullback.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
instance towerPull_additive : (towerPull l E g).Additive := inferInstanceAs
  (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pull l E g)).Additive)

/-- The universal derived strict tower pullback, with objectwise K-flat computation.
Source: Stacks 06YS, 06YY, 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: resolve strict diagrams by objectwise flat-term K-flat complexes; ordinary
ringed pullback preserves quasi-isomorphisms between these. Apply the resolving-class
left-derived theorem to the termwise additive functor. Its shifts are the derived
termwise shifts, and it is computed on every objectwise K-flat tower. -/
theorem towerPull_exists :
    ∃ (V : DerivedCategory (Towers l E Y) ⥤ DerivedCategory (Towers l E X))
      (ε : DerivedCategory.Q ⋙ V ⟶
        (towerPull l E g).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      V.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Towers l E Y) (.up ℤ)) ∧
      (∃ (_ : V.CommShift ℤ), V.IsTriangulated) ∧
      ∀ P : CochainComplex (Towers l E Y) ℤ,
        (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E Y)
            (P.asFunctor.obj (op n))) → IsIso (ε.app P) := by
  classical
  let A := Towers l E Y
  let B := Towers l E X
  let T := (towerPull l E g).mapHomologicalComplex (.up ℤ)
  let H := HomotopyCategory.quotient A (.up ℤ)
  let F := (towerPull l E g).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let good : CochainComplex A ℤ → Prop := fun P ↦
    ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P.asFunctor.obj (op n))
  have hres₀ (P : CochainComplex A ℤ) :
      ∃ (L : CochainComplex A ℤ) (a : L ⟶ P), good L ∧ QuasiIso a := by
    obtain ⟨G, η, hη, hk, _⟩ := SheafOfModules.functorial_resolution
      (completedIntegralCommRingSheafUnrestricted l E Y)
    let L := (transpose l E Y).obj (P.asFunctor ⋙ G)
    let a : L ⟶ P := (transpose l E Y).map (Functor.whiskerLeft P.asFunctor η)
    refine ⟨L, a, fun n ↦ hk (P.asFunctor.obj (op n)), ?_⟩
    exact (HomologicalComplex.quasiIso_iff_evaluation a).2
      (fun n ↦ hη (P.asFunctor.obj n))
  have hpres {P Q : CochainComplex A ℤ} (a : P ⟶ Q) (hp : good P) (hq : good Q)
      (ha : QuasiIso a) : QuasiIso (T.map a) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    exact pull_quasiIso l E g
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app n)
      (hp n.unop) (hq n.unop) ((HomologicalComplex.quasiIso_iff_evaluation a).1 ha n)
  exact deriveOfComplexResolutions (towerPull l E g) good hres₀ hpres

/-- The universal derived functor V_g before completion or inverse limit.
Source: Stacks 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def derivedPull : DerivedCategory (Towers l E Y) ⥤ DerivedCategory (Towers l E X) :=
  (towerPull_exists l E g).choose

/-- The universal counit, retaining the actual strict tower representative.
Source: Stacks 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def derivedCounit : DerivedCategory.Q ⋙ derivedPull l E g ⟶
    (towerPull l E g).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (towerPull_exists l E g).choose_spec.choose

end WeilConjectures.CompletedTowerIndependent
