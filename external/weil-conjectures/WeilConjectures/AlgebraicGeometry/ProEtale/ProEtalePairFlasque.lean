/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

import WeilConjectures.AlgebraicGeometry.SupportCounterexample.ProEtaleInfiniteClopenPair
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian

/-!
# Supported sections and flasqueness for a pro-etale open-closed pair

The existing `finiteSupportedSections` and `finiteClosedUpperShriek` give the kernel functor
and its closed inverse image. Constant-coefficient module sheaves are presented as
sheaves valued in `ModuleCat`, without a constructibility condition.

## References

* Stacks Project, Tags 03DA, 09BN and 09AH
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison `G_Z ⟶ s_*s^!`, obtained by applying the closed
adjunction unit to the supported kernel. It is defined even when the open complement
is not quasi-compact. -/
noncomputable def finiteSupportedClosedComparison (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X) :
    finiteSupportedSections Λ j ⟶
      finiteClosedUpperShriek Λ s j ⋙ lowerStar (ModuleCat.{u + 1} Λ) s :=
  Functor.whiskerLeft (finiteSupportedSections Λ j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit

private local instance moduleSheaf_colimits (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) := by
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ X
  exact IsGrothendieckAbelian.hasColimits _

/-- Both the supported-kernel functor and its closed inverse image are left exact. -/
theorem finiteSupportedSections_leftExact (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z U : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hPair : IsCompl (Set.range s) (Set.range j)) :
    PreservesFiniteLimits (finiteSupportedSections Λ j) ∧
      PreservesFiniteLimits (finiteClosedUpperShriek Λ s j) := by
  have _ := hPair
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let D := parallelPair
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit 0
  have hD : PreservesFiniteLimits D.flip :=
    preservesFiniteLimits_of_evaluation _ (fun p ↦ by
      cases p
      · change PreservesFiniteLimits (𝟭 C)
        infer_instance
      · change PreservesFiniteLimits
          (upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j)
        infer_instance)
  have hG : PreservesFiniteLimits (finiteSupportedSections Λ j) := by
    exact preservesFiniteLimits_of_natIso (limitIsoFlipCompLim D).symm
  exact ⟨hG, comp_preservesFiniteLimits _ _⟩

/-- With quasi-compact open complement, the specified natural comparison is an
isomorphism. -/
theorem finiteSupportedClosedComparison_isIso (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {X Z U : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range s) (Set.range j)) :
    IsIso (finiteSupportedClosedComparison Λ s j) := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let L := upperStar (ModuleCat.{u + 1} Λ) j
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  have hz (M : C) : IsZero (L.obj ((finiteSupportedSections Λ j).obj M)) := by
    have hm : Mono (L.map (adj.unit.app M)) := by
      constructor
      intro Y a b hab
      have he := congrArg (fun f ↦ f ≫ adj.counit.app (L.obj M)) hab
      have ht : L.map (adj.unit.app M) ≫ adj.counit.app (L.obj M) = 𝟙 _ :=
        adj.left_triangle_components M
      simpa only [Category.assoc, ht, Category.comp_id] using he
    let e : (finiteSupportedSections Λ j).obj M ≅ kernel (adj.unit.app M) :=
      PreservesKernel.iso ((evaluation C C).obj M) adj.unit
    exact (isZero_kernel_of_mono (L.map (adj.unit.app M))).of_iso
      (L.mapIso e ≪≫ PreservesKernel.iso L (adj.unit.app M))
  have hi (M : C) : IsIso ((finiteSupportedClosedComparison Λ s j).app M) :=
    isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl s j hPair _ (hz M)
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale
