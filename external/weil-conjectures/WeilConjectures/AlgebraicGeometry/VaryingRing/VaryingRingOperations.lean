/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
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
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.SmoothPurity.NormalizedLeftExtension
import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import Mathlib.CategoryTheory.Sites.Limits
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
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.CoverPreserving
import all Mathlib.CategoryTheory.Iso -- scalar-inverse unfolding in section comparisons
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator

/-!
# Geometric operations for varying constant coefficient rings

Source: Stacks Project, Tags 03DI, 03DJ, 07A6, 09AE and 0F7B;
Zheng, Construction 4.1 (blueprint: def-sp-varying-ring-operations).

Systems and their ordinary unbounded derived categories are the existing sequence-site
module categories. Direct image is actual continuous module pushforward. Its left adjoint,
and open extension, are selected by their universal properties; all compositors are
unit-preserving adjoint comparisons.

## Main definitions

- `Modules`, `Derived`: the existing semilinear categories.
- `push`, `pull`, `extension`, `P`, `G`, `J`: actual ordinary and derived operations.
- `modulePComp`, `gComp`, `pComp`, `jComp`: normalized composition.
- `evalG`, `evalP`, `evalJ`: canonical coefficient evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

attribute [-instance] SemilinearSections.evaluationContinuous
private local instance evaluationContinuousFixed {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) :=
  SemilinearSections.evaluationContinuous.{u + 1, u, u + 1} J n

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The small pro-etale site fits the coefficient universe, retaining Hom universe u.
Source: Stacks 098K (blueprint: def-sp-varying-ring-operations). -/
instance siteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The vertical sequence site has the same smallness bound.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance sequenceSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Ring-valued sheafification with all site and value universes fixed explicitly.
Source: Stacks 00W1 (blueprint: def-sp-varying-ring-operations). -/
instance ringSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  HasSmallSiteSheafify.hasSheafify_of_essentiallySmall.{u + 2, u, u, u + 1}
    CommRingCat.{u + 1} (Scheme.ProEt.topology X)

/-- Constant coefficient sheaves, with arbitrary commutative rings.
Source: Stacks 00YV (blueprint: def-sp-varying-ring-operations). -/
abbrev coefficients (X : Scheme.{u}) (n : ℕ) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (R n)

/-- The actual adjacent ring-sheaf maps.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def coefficientTransition (X : Scheme.{u}) (n : ℕ) :
    coefficients R X (n + 1) ⟶ coefficients R X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (φ n)

/-- The already constructed module category on the vertical sequence site.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev Modules (X : Scheme.{u}) :=
  Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X)

/-- Its ordinary unbounded derived category, with no cartesianness condition.
Source: Stacks 05RU (blueprint: def-sp-varying-ring-operations). -/
abbrev Derived (X : Scheme.{u}) :=
  DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)

/-- The functor on sequence sites leaves the coefficient index unchanged.
Source: Stacks 09AE; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def baseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- Continuity on the vertical sequence topology.
Source: Stacks 09AE; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: the inverse image of a vertical covering sieve is the base change of its
covering slice. Pro-etale base change preserves covering families. The horizontal
coordinate is unchanged, so the vertical-slice criterion proves continuity. -/
theorem baseChange_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (baseChange f).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  have : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  have : RepresentablyFlat (baseChange f) := by
    constructor
    intro U
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ) (Scheme.proEtaleBaseChange f)).symm
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  constructor
  intro U S hS
  change (S.functorPushforward (baseChange f)).functorPullback (Prod.sectR U.1 X.ProEt) ∈
    Scheme.ProEt.topology X ((Scheme.proEtaleBaseChange f).obj U.2)
  apply (Scheme.ProEt.topology X).superset_covering _
    ((Scheme.proEtaleBaseChangeCoverPreserving f).cover_preserve hS)
  intro V a ha
  obtain ⟨W, g, h, hg, rfl⟩ := ha
  exact ⟨(U.1, W), Prod.mkHom (𝟙 U.1) g, Prod.mkHom (𝟙 U.1) h, hg, by
    ext <;> simp [baseChange]⟩

attribute [instance] baseChange_continuous

/-- The coefficient structure map at a sequence-site object is the canonical map on
constant sections at that same index.
Source: Stacks 00YV, 09AE (blueprint: def-sp-varying-ring-operations). -/
def ringMapApp {X Y : Scheme.{u}} (f : X ⟶ Y) (U : (ℕ × Y.ProEt)ᵒᵖ) :
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj
        ((coefficients R Y U.unop.1).obj.obj (op U.unop.2)) ⟶
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj
        ((coefficients R X U.unop.1).obj.obj
          ((Scheme.proEtaleBaseChange f).op.obj (op U.unop.2))) :=
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1} (R U.unop.1)).hom.app
      (op U.unop.2))

private theorem constantMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    _ _) ((presheafToSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange f).op.obj U))
    ((toSheafification (Scheme.ProEt.topology X) CommRingCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

/-- Naturality includes the horizontal, possibly nonflat, coefficient maps.
Source: Stacks 00YV; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: for vertical arrows use naturality of the constant-section map on the site;
for horizontal arrows use its naturality in the coefficient ring. Every product
arrow factors into these two arrows, giving the displayed naturality equation. -/
theorem ringMapApp_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : (ℕ × Y.ProEt)ᵒᵖ} (a : U ⟶ V) :
    (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) (coefficients R Y)
        (coefficientTransition R φ Y))).obj.map a ≫ ringMapApp R f V =
      ringMapApp R f U ≫
        (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
            (coefficientTransition R φ X))).obj.map ((baseChange f).op.map a) := by
  let δ : rings (Scheme.ProEt.topology Y) (coefficients R Y)
      (coefficientTransition R φ Y) ⟶
      rings (Scheme.ProEt.topology X) (coefficients R X)
        (coefficientTransition R φ X) ⋙
          Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1} :=
    NatTrans.ofOpSequence
      (fun n ↦ Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (R n))
      (by
        intro n
        dsimp only [rings, Functor.comp_map]
        simp only [Functor.ofOpSequence_map_homOfLE_succ]
        exact constantMap_naturality f (φ n))
  let ε := Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := Y.ProEt)).functor
    (Functor.uncurry.map
      (Functor.whiskerRight δ (sheafToPresheaf (Scheme.ProEt.topology Y)
        CommRingCat.{u + 1})))
  exact (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).congr_map (ε.naturality a)

/-- The real ring-sheaf map defining direct image on semilinear systems.
Source: Stacks 03DA; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def ringMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) (coefficients R Y)
          (coefficientTransition R φ Y)) ⟶
      ((baseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
            (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
              (coefficientTransition R φ X))) :=
  ⟨{ app := ringMapApp R f, naturality := fun _ _ a => ringMapApp_naturality R φ f a }⟩

/-- Direct image retains sections M_n(H ×_Y X) and their semilinear transitions.
Source: Stacks 03DA; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def push {X Y : Scheme.{u}} (f : X ⟶ Y) : Modules R φ X ⥤ Modules R φ Y :=
  SheafOfModules.pushforward (ringMap R φ f)

private abbrev sequenceRing (X : Scheme.{u}) :=
  ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
      (coefficientTransition R φ X))

private theorem sequenceRing_map_vertical (X : Scheme.{u}) (n : ℕ)
    {U V : X.ProEt} (a : U ⟶ V) :
    (sequenceRing R φ X).obj.map (Prod.mkHom (𝟙 n) a).op =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((coefficients R X n).obj.map a.op) := by
  change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    (((rings (Scheme.ProEt.topology X) (coefficients R X)
      (coefficientTransition R φ X)).map (𝟙 (op n))).hom.app (op V) ≫
        (coefficients R X n).obj.map a.op) = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private def smallModelEquivalence {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (A : Sheaf J RingCat.{u + 1}) :
    SheafOfModules.{u + 1}
      (((AsSmall.down : AsSmall.{u + 1} C ⥤ C).sheafPushforwardContinuous
        RingCat.{u + 1} (AsSmall.down.inducedTopology J) J).obj A) ≌
      SheafOfModules.{u + 1} A := by
  let K := (AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology J
  let B := ((AsSmall.down : AsSmall.{u + 1} C ⥤ C).sheafPushforwardContinuous
    RingCat.{u + 1} K J).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := C)).functor.IsContinuous J K :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := C)).functor.IsContinuous
      J ((AsSmall.equiv.{u, u + 1, u + 1} (C := C)).inverse.inducedTopology J))
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := C)).inverse.IsContinuous K J := by
    change AsSmall.down.IsContinuous K J
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := C)) (𝟙 A) (𝟙 B)
    (by
      apply NatTrans.ext
      funext U
      change B.obj.map (𝟙 U) = 𝟙 _ ≫ 𝟙 _
      rw [CategoryTheory.Functor.map_id, Category.id_comp])
    (by
      apply NatTrans.ext
      funext U
      change (𝟙 _ ≫ 𝟙 _) ≫ A.obj.map (𝟙 U) = 𝟙 _
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp])

private theorem largePush_isRightAdjoint
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous JC JD]
    (A : Sheaf JC RingCat.{u + 1}) (B : Sheaf JD RingCat.{u + 1})
    (a : A ⟶ (F.sheafPushforwardContinuous RingCat JC JD).obj B) :
    (SheafOfModules.pushforward.{u + 1} a).IsRightAdjoint := by
  let KC := (AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology JC
  let KD := (AsSmall.down : AsSmall.{u + 1} D ⥤ D).inducedTopology JD
  have : (AsSmall.up : D ⥤ AsSmall.{u + 1} D).IsContinuous JD KD :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := D)).functor.IsContinuous
      JD ((AsSmall.equiv.{u, u + 1, u + 1} (C := D)).inverse.inducedTopology JD))
  let G : AsSmall.{u + 1} C ⥤ AsSmall.{u + 1} D :=
    AsSmall.down ⋙ F ⋙ AsSmall.up
  have := Functor.isContinuous_comp F (AsSmall.up : D ⥤ AsSmall.{u + 1} D) JC JD KD
  have : G.IsContinuous KC KD :=
    Functor.isContinuous_comp AsSmall.down (F ⋙ AsSmall.up) KC JC KD
  let AC := ((AsSmall.down : AsSmall.{u + 1} C ⥤ C).sheafPushforwardContinuous
    RingCat.{u + 1} KC JC).obj A
  let BD := ((AsSmall.down : AsSmall.{u + 1} D ⥤ D).sheafPushforwardContinuous
    RingCat.{u + 1} KD JD).obj B
  let b : AC ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} KC KD).obj BD :=
    ⟨Functor.whiskerLeft AsSmall.down.op a.hom⟩
  let eD := smallModelEquivalence JD B
  let eC := smallModelEquivalence JC A
  let adj := eC.symm.toAdjunction.comp
    ((SheafOfModules.pullbackPushforwardAdjunction b).comp eD.toAdjunction)
  refine (adj.ofNatIsoRight ?_).isRightAdjoint
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    dsimp only [eD, eC, smallModelEquivalence]
    exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
  · intro M N c
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

/-- Existence of inverse image as the left adjoint of the actual section functor.
Source: Stacks 03EK; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: form inverse image on the product site and extend scalars along ringMap.
Constant sheaves pull back to the same constants, compatibly with φ. Thus this
module pullback is the componentwise inverse image and has the usual adjunction. -/
theorem push_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (push R φ f).IsRightAdjoint := by
  exact largePush_isRightAdjoint (C := ℕ × Y.ProEt) (D := ℕ × X.ProEt)
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X)) (baseChange f)
    (sequenceRing R φ Y) (sequenceRing R φ X) (ringMap R φ f)

attribute [instance] push_isRightAdjoint

/-- Inverse image selected by its universal property, not by a noncanonical map.
Source: Stacks 03EK (blueprint: def-sp-varying-ring-operations). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := (push R φ f).leftAdjoint

/-- The universal-property adjunction fixes every subsequent mate and compositor.
Source: Stacks 03EK (blueprint: def-sp-varying-ring-operations). -/
def moduleAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : pull R φ f ⊣ push R φ f :=
  Adjunction.ofIsRightAdjoint _

attribute [local irreducible] moduleAdj

/-- Direct image is additive on all section modules.
Source: Stacks 03DA (blueprint: def-sp-varying-ring-operations).
Proof: continuous module pushforward preserves the underlying maps and their
pointwise sums. Extensionality on all sections gives additivity. -/
theorem push_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (push R φ f).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

attribute [instance] push_additive

private theorem towerEvaluation_isRightAdjoint
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : ℕ → Sheaf J CommRingCat.{u + 1})
    (α : ∀ n, A (n + 1) ⟶ A n) (n : ℕ) :
    (SemilinearSections.evaluation.{u + 1, u, u + 1} J A α n).IsRightAdjoint := by
  let := evaluationContinuous.{u + 1, u, u + 1} J n
  exact largePush_isRightAdjoint J (coefficientSequenceTopology J) (Prod.sectR n C)
    (ring.{u + 1, u, u + 1} J (A n))
    (ring.{u + 1, u, u + 1} (coefficientSequenceTopology J)
      (systemRing.{u + 1, u, u + 1} J A α))
    (eqToHom (evaluation_ring.{u + 1, u, u + 1} J A α n).symm)

private theorem preservesLimits_underlyingEvaluation
    {M : Type (u + 2)} [Category.{u + 1} M]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {A : Sheaf J RingCat.{u + 1}} {B : Sheaf K RingCat.{u + 1}}
    (a : A ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj B)
    (T : M ⥤ SheafOfModules.{u + 1} B)
    (h : PreservesLimits (T ⋙ SheafOfModules.pushforward a)) (U : Cᵒᵖ) :
    PreservesLimits
      ((T ⋙ (SheafOfModules.forget B ⋙ PresheafOfModules.toPresheaf B.obj)) ⋙
        (CategoryTheory.evaluation Dᵒᵖ AddCommGrpCat.{u + 1}).obj (F.op.obj U)) := by
  let := h
  have : PreservesLimits
      (((T ⋙ SheafOfModules.pushforward a) ⋙
        (SheafOfModules.forget A ⋙ PresheafOfModules.toPresheaf A.obj)) ⋙
        (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u + 1}).obj U) := by
    infer_instance
  exact this

private theorem towerFunctor_preservesLimits
    {M : Type (u + 2)} [Category.{u + 1} M]
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : ℕ → Sheaf J CommRingCat.{u + 1})
    (α : ∀ n, A (n + 1) ⟶ A n)
    (F : M ⥤ Systems.{u + 1, u, u + 1} J A α)
    (H : ∀ n, M ⥤ SemilinearSections.Mod.{u + 1, u, u + 1} J (A n))
    [∀ n, PreservesLimits (H n)]
    (e : ∀ n, F ⋙ SemilinearSections.evaluation.{u + 1, u, u + 1} J A α n ≅ H n) :
    PreservesLimits F := by
  let T : Systems.{u + 1, u, u + 1} J A α ⥤
      (ℕ × C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _
  have : ReflectsLimits T := reflectsLimits_of_reflectsIsomorphisms
  have : PreservesLimits (F ⋙ T) := by
    apply preservesLimits_of_evaluation
    intro V
    have hEval : PreservesLimits (F ⋙
        SemilinearSections.evaluation.{u + 1, u, u + 1} J A α V.unop.1) :=
      preservesLimits_of_natIso (e V.unop.1).symm
    let := evaluationContinuous.{u + 1, u, u + 1} J V.unop.1
    exact preservesLimits_underlyingEvaluation
      (M := M) (C := C) (D := ℕ × C) (J := J) (K := coefficientSequenceTopology J)
      (A := ring.{u + 1, u, u + 1} J (A V.unop.1))
      (B := ring.{u + 1, u, u + 1} (coefficientSequenceTopology J)
        (systemRing.{u + 1, u, u + 1} J A α))
      (Prod.sectR V.unop.1 C) (eqToHom (evaluation_ring.{u + 1, u, u + 1} J A α V.unop.1).symm)
      F hEval (op V.unop.2)
  exact preservesLimits_of_reflects_of_preserves F T

/-- Exact ordinary evaluation of a semilinear system.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev eval (X : Scheme.{u}) (n : ℕ) :
    Modules R φ X ⥤ StrictTower.Modules (R n) X :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X) n

private theorem moduleFunctorIso_ext
    {M : Type (u + 2)} [Category.{u + 1} M]
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A : Sheaf J RingCat.{u + 1}} {F H : M ⥤ SheafOfModules.{u + 1} A}
    (d e : F ≅ H)
    (h : ∀ (N : M) (U : Cᵒᵖ) (x : (F.obj N).val.obj U),
      (d.hom.app N).val.app U x = (e.hom.app N).val.app U x) : d = e := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact h N U x

private theorem sequencePushforwardEvaluation
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)] (n : ℕ)
    [(Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    [(Prod.sectR n D).IsContinuous K (coefficientSequenceTopology K)]
    {A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}}
    {B : Sheaf (coefficientSequenceTopology K) RingCat.{u + 1}}
    {S : Sheaf J RingCat.{u + 1}} {T : Sheaf K RingCat.{u + 1}}
    (a : S ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1}
      J (coefficientSequenceTopology J)).obj A)
    (b : T ⟶ ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{u + 1}
      K (coefficientSequenceTopology K)).obj B)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj T)
    (h : ∀ U : Cᵒᵖ,
      a.hom.app U ≫ φ.hom.app (op (n, U.unop)) =
        ψ.hom.app U ≫ b.hom.app (F.op.obj U)) :
    ∃! d : SheafOfModules.pushforward.{u + 1} φ ⋙ SheafOfModules.pushforward a ≅
        SheafOfModules.pushforward b ⋙ SheafOfModules.pushforward ψ,
      ∀ (N : SheafOfModules.{u + 1} B) (U : C)
        (x : ((SheafOfModules.pushforward φ).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op U) x = x := by
  have := Functor.isContinuous_comp (Prod.sectR n C) ((𝟭 ℕ).prod F)
    J (coefficientSequenceTopology J) (coefficientSequenceTopology K)
  have := Functor.isContinuous_comp F (Prod.sectR n D)
    J K (coefficientSequenceTopology K)
  have he : a ≫ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1}
      J (coefficientSequenceTopology J)).map φ =
      ψ ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact h U
  let d : SheafOfModules.pushforward.{u + 1} φ ⋙ SheafOfModules.pushforward a ≅
      SheafOfModules.pushforward b ⋙ SheafOfModules.pushforward ψ :=
    SheafOfModules.pushforwardComp a φ ≪≫ SheafOfModules.pushforwardCongr he ≪≫
      (SheafOfModules.pushforwardComp ψ b).symm
  refine ⟨d, fun _ _ _ ↦ rfl, ?_⟩
  intro d' hd'
  apply moduleFunctorIso_ext d' d
  intro N U x
  exact hd' N U.unop x

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem towerPushforwardEvaluation
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : ℕ → Sheaf J CommRingCat.{u + 1}) (α : ∀ n, A (n + 1) ⟶ A n)
    (B : ℕ → Sheaf K CommRingCat.{u + 1}) (β : ∀ n, B (n + 1) ⟶ B n) (n : ℕ)
    (φ : ring.{u + 1, u, u + 1} (coefficientSequenceTopology J)
        (systemRing.{u + 1, u, u + 1} J A α) ⟶
      (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj
          (ring.{u + 1, u, u + 1} (coefficientSequenceTopology K)
            (systemRing.{u + 1, u, u + 1} K B β)))
    (ψ : ring.{u + 1, u, u + 1} J (A n) ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj
        (ring.{u + 1, u, u + 1} K (B n)))
    (h : ∀ U : Cᵒᵖ, φ.hom.app (op (n, U.unop)) = ψ.hom.app U) :
    type_of% (let _instSliceC :=
        SemilinearSections.evaluationContinuous.{u + 1, u, u + 1} J n
      let _instSliceD := SemilinearSections.evaluationContinuous.{u + 1, u, u + 1} K n
      sequencePushforwardEvaluation (C := C) (D := D)
      (A := ring.{u + 1, u, u + 1} (coefficientSequenceTopology J)
        (systemRing.{u + 1, u, u + 1} J A α))
      (B := ring.{u + 1, u, u + 1} (coefficientSequenceTopology K)
        (systemRing.{u + 1, u, u + 1} K B β))
      (S := ring.{u + 1, u, u + 1} J (A n))
      (T := ring.{u + 1, u, u + 1} K (B n)) J K F n
      (eqToHom (evaluation_ring.{u + 1, u, u + 1} J A α n).symm)
      (eqToHom (evaluation_ring.{u + 1, u, u + 1} K B β n).symm) φ ψ (by
        intro U
        rw [ObjectProperty.eqToHom_hom, eqToHom_app,
          ObjectProperty.eqToHom_hom, eqToHom_app]
        change (𝟙 _ : _ ⟶ _) ≫ φ.hom.app (op (n, U.unop)) =
          ψ.hom.app U ≫ (𝟙 _ : _ ⟶ _)
        rw [Category.id_comp, Category.comp_id]
        exact h U)) :=
  let _instSliceC := SemilinearSections.evaluationContinuous.{u + 1, u, u + 1} J n
  let _instSliceD := SemilinearSections.evaluationContinuous.{u + 1, u, u + 1} K n
  sequencePushforwardEvaluation (C := C) (D := D)
      (A := ring.{u + 1, u, u + 1} (coefficientSequenceTopology J)
        (systemRing.{u + 1, u, u + 1} J A α))
      (B := ring.{u + 1, u, u + 1} (coefficientSequenceTopology K)
        (systemRing.{u + 1, u, u + 1} K B β))
      (S := ring.{u + 1, u, u + 1} J (A n))
      (T := ring.{u + 1, u, u + 1} K (B n)) J K F n
      (eqToHom (evaluation_ring.{u + 1, u, u + 1} J A α n).symm)
      (eqToHom (evaluation_ring.{u + 1, u, u + 1} K B β n).symm) φ ψ (by
        intro U
        rw [ObjectProperty.eqToHom_hom, eqToHom_app,
          ObjectProperty.eqToHom_hom, eqToHom_app]
        change (𝟙 _ : _ ⟶ _) ≫ φ.hom.app (op (n, U.unop)) =
          ψ.hom.app U ≫ (𝟙 _ : _ ⟶ _)
        rw [Category.id_comp, Category.comp_id]
        exact h U)

private local instance prodBaseContinuous {U X : Scheme.{u}} (j : U ⟶ X) :
    ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange j)).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceTopology (Scheme.ProEt.topology U)) := baseChange_continuous j

private theorem moduleEvalP_specialized {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    type_of% (
      let _instProduct : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)).IsContinuous
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X)) := baseChange_continuous f
      towerPushforwardEvaluation (C := Y.ProEt) (D := X.ProEt)
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (Scheme.proEtaleBaseChange f) (coefficients R Y) (coefficientTransition R φ Y)
      (coefficients R X) (coefficientTransition R φ X) n (ringMap R φ f)
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (Scheme.proEtaleRingDirectImageMap f (coefficients R Y n) (coefficients R X n)
          (StrictTower.constantRingIso (R n) f))) (by
        intro U
        have hb : Scheme.proEtaleRingDirectImageMap f (coefficients R Y n)
            (coefficients R X n) (StrictTower.constantRingIso (R n) f) =
            Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (R n) :=
          ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
            _
        exact congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          (t.hom.app U)) hb.symm)) :=
  let _instProduct : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)).IsContinuous
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X)) := baseChange_continuous f
  towerPushforwardEvaluation (C := Y.ProEt) (D := X.ProEt)
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (Scheme.proEtaleBaseChange f) (coefficients R Y) (coefficientTransition R φ Y)
      (coefficients R X) (coefficientTransition R φ X) n (ringMap R φ f)
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (Scheme.proEtaleRingDirectImageMap f (coefficients R Y n) (coefficients R X n)
          (StrictTower.constantRingIso (R n) f))) (by
        intro U
        have hb : Scheme.proEtaleRingDirectImageMap f (coefficients R Y n)
            (coefficients R X n) (StrictTower.constantRingIso (R n) f) =
            Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (R n) :=
          ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
            _
        exact congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          (t.hom.app U)) hb.symm)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Elaborating the section-carrier normalization unfolds both continuous module functors.
/-- Ordinary pushforward evaluation is identity on every section carrier.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: both sides have sections N_n(H ×_Y X), maps induced by the same restrictions,
and the same constant scalar map. The identity is linear and natural. Equality on
all sections proves uniqueness. -/
theorem moduleEvalP_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : push R φ f ⋙ eval R φ Y n ≅
        eval R φ X n ⋙ StrictTower.moduleDirectImage (R n) f,
      ∀ (N : Modules R φ X) (U : Y.ProEt)
        (x : ((push R φ f).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op U) x = x :=
  moduleEvalP_specialized R φ f n

/-- The actual componentwise direct-image identification.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def moduleEvalP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    push R φ f ⋙ eval R φ Y n ≅
      eval R φ X n ⋙ StrictTower.moduleDirectImage (R n) f :=
  (moduleEvalP_existsUnique R φ f n).choose

section EvaluationRightAdjoint

universe c v k

variable {C : Type (u + 1)} [Category.{u} C]
private local instance sliceContinuous (J : GrothendieckTopology C) (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) :=
  evaluationContinuous.{u + 1, u, u + 1} J n
variable (A : (ℕ × C)ᵒᵖ ⥤ RingCat.{u + 1}) (n : ℕ)
private def hor (V : (ℕ × C)ᵒᵖ) (h : n ≤ V.unop.1) :
    V ⟶ op (n, V.unop.2) := (Prod.mkHom (homOfLE h) (𝟙 V.unop.2)).op
private abbrev coValue (M : PresheafOfModules.{u + 1} ((Prod.sectR n C).op ⋙ A))
    (V : (ℕ × C)ᵒᵖ) : ModuleCat.{u + 1} (A.obj V) :=
  ModuleCat.of (A.obj V)
    (∀ h : PLift (n ≤ V.unop.1),
      (ModuleCat.restrictScalars (A.map (hor n V h.down)).hom).obj (M.obj (op V.unop.2)))
private def coObj (M : PresheafOfModules.{u + 1} ((Prod.sectR n C).op ⋙ A)) :
    PresheafOfModules.{u + 1} A where
  obj := coValue A n M
  map {V W} a := ModuleCat.ofHom (X := coValue A n M V)
    (Y := (ModuleCat.restrictScalars (A.map a).hom).obj (coValue A n M W))
    { toFun := fun x h ↦ M.map a.unop.2.op (x ⟨h.down.trans (leOfHom a.unop.1)⟩)
      map_add' := by intros; funext h; exact map_add _ _ _
      map_smul' := by
        intro r x
        funext h
        change M.map a.unop.2.op
          ((A.map (hor n V (h.down.trans (leOfHom a.unop.1)))) r • x _) =
          (A.map (hor n W h.down)) ((A.map a) r) • M.map a.unop.2.op (x _)
        rw [M.map_smul]
        congr 1
        change (A.map (hor n V _) ≫ A.map ((Prod.sectR n C).map a.unop.2).op) r =
          (A.map a ≫ A.map (hor n W h.down)) r
        rw [← A.map_comp, ← A.map_comp]
        congr 2
        apply congrArg A.map
        apply Quiver.Hom.unop_inj
        apply Prod.hom_ext
        · apply Subsingleton.elim
        · simp [hor] }
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change M.map (𝟙 V.unop.2).op (x _) = x h
    rw [op_id, M.map_id]
    rfl
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change M.map (b.unop.2 ≫ a.unop.2).op (x _) =
      M.map b.unop.2.op (M.map a.unop.2.op (x _))
    rw [op_comp, M.map_comp_apply]
private theorem sequence_isSheaf_of_slices {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ Type k)
    (hP : ∀ n : ℕ, Presieve.IsSheaf J ((Prod.sectR n C).op ⋙ P)) :
    Presieve.IsSheaf (coefficientSequenceTopology J) P := by
  intro X S hS x hx
  let xv : Presieve.FamilyOfElements ((Prod.sectR X.1 C).op ⋙ P)
      (S.functorPullback (Prod.sectR X.1 C)).arrows :=
    fun Y f hf ↦ x ((Prod.sectR X.1 C).map f) hf
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx ((Prod.sectR X.1 C).map g₁) ((Prod.sectR X.1 C).map g₂)
      hf₁ hf₂ (by simpa only [← Functor.map_comp] using
        (congrArg (fun f ↦ (Prod.sectR X.1 C).map f) he))
  obtain ⟨a, ha, hua⟩ := hP X.1 _ hS xv hxv
  refine ⟨a, ?_, ?_⟩
  · intro Y f hf
    apply ((hP Y.1).isSeparated _ (J.pullback_stable f.2 hS)).ext
    intro Z g hg
    let v : (X.1, Z) ⟶ X := (Prod.sectR X.1 C).map (g ≫ f.2)
    let k : (Y.1, Z) ⟶ (X.1, Z) := Prod.mkHom f.1 (𝟙 Z)
    have hv : S v := hg
    have he : k ≫ v = (Prod.sectR Y.1 C).map g ≫ f := by
      ext <;> simp [k, v]
    have hc := hx k ((Prod.sectR Y.1 C).map g) hv hf he
    have hag := congrArg (P.map k.op) (ha (g ≫ f.2) hv)
    change P.map ((Prod.sectR Y.1 C).map g).op (P.map f.op a) = _
    erw [← P.map_comp_apply, ← op_comp, ← he]
    have hp : P.map (k ≫ v).op a = P.map k.op (P.map v.op a) := by
      rw [op_comp, P.map_comp]
      rfl
    exact hp.trans (hag.trans hc)
  · intro b hb
    apply hua b
    intro Y f hf
    exact hb ((Prod.sectR X.1 C).map f) hf

private def coSheaf (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J)
      RingCat.{u + 1}) (n : ℕ)
    (M : SheafOfModules.{u + 1}
      (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1} J
        (coefficientSequenceTopology J)).obj A)) :
    SheafOfModules.{u + 1} A where
  val := coObj A.obj n M.val
  isSheaf := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat.{u + 1}),
      isSheaf_iff_isSheaf_of_type]
    apply sequence_isSheaf_of_slices
    intro m U S hS x hx
    have hM : Presieve.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat.{u + 1}) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        ((Presheaf.isSheaf_iff_isSheaf_forget J _
          (forget AddCommGrpCat.{u + 1})).mp M.isSheaf)
    have hh (h : PLift (n ≤ m)) := hM S hS
      (fun {V} f hf ↦ x f hf h)
      (by
        intro V W Z a b f g hf hg hab
        exact congrFun (hx a b hf hg hab) h)
    choose a ha hu using hh
    refine ⟨fun h ↦ a h, ?_, ?_⟩
    · intro V f hf
      funext h
      exact ha h f hf
    · intro b hb
      funext h
      apply hu h (b h)
      intro V f hf
      exact congrFun (hb f hf) h

private def coFunctor (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}) (n : ℕ) :
    SheafOfModules.{u + 1}
      (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1} J
        (coefficientSequenceTopology J)).obj A) ⥤ SheafOfModules.{u + 1} A where
  obj := coSheaf J A n
  map {M N} f :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (X := coValue A.obj n M.val V)
          (Y := coValue A.obj n N.val V)
          { toFun := fun x h ↦ f.val.app (op V.unop.2) (x h)
            map_add' := by intros; funext h; exact map_add _ _ _
            map_smul' := by intros; funext h; exact map_smul _ _ _ }
        naturality := by
          intro V W a
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext h
          exact PresheafOfModules.naturality_apply f.val a.unop.2.op (x _) } }

private def ev₀ (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}) (n : ℕ) :=
  SheafOfModules.pushforward.{u + 1} (F := Prod.sectR n C)
    (𝟙 (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1} J
      (coefficientSequenceTopology J)).obj A))

private def coUnit (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}) (n : ℕ) :
    𝟭 (SheafOfModules.{u + 1} A) ⟶ ev₀ J A n ⋙ coFunctor J A n where
  app N :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (X := N.val.obj V)
          (Y := coValue A.obj n ((ev₀ J A n).obj N).val V)
          { toFun := fun x h ↦ N.val.map (hor n V h.down) x
            map_add' := by intros; funext h; exact map_add _ _ _
            map_smul' := by intros; funext h; exact N.val.map_smul _ _ _ }
        naturality := by
          intro V W a
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext h
          change N.val.map (hor n W h.down) (N.val.map a x) =
            N.val.map ((Prod.sectR n C).map a.unop.2).op (N.val.map (hor n V _) x)
          refine (N.val.map_comp_apply a (hor n W h.down) x).symm.trans
            ((N.val.congr_map_apply
              (f := a ≫ hor n W h.down)
              (g := hor n V (h.down.trans (leOfHom a.unop.1)) ≫
                ((Prod.sectR n C).map a.unop.2).op) ?_ x).trans
              (N.val.map_comp_apply (hor n V (h.down.trans (leOfHom a.unop.1)))
                ((Prod.sectR n C).map a.unop.2).op x))
          apply Quiver.Hom.unop_inj
          apply Prod.hom_ext
          · apply Subsingleton.elim
          · simp [hor] } }
  naturality {M N} f := by
    ext V x
    funext h
    exact (PresheafOfModules.naturality_apply f.val (hor n V h.down) x).symm

private def coCounit (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}) (n : ℕ) :
    coFunctor J A n ⋙ ev₀ J A n ⟶ 𝟭 _ where
  app M :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom
          (X := ((ev₀ J A n).obj ((coFunctor J A n).obj M)).val.obj V)
          (Y := M.val.obj V)
          { toFun := fun x ↦ x ⟨le_refl n⟩
            map_add' := by intros; rfl
            map_smul' := by
              intro r x
              have hs : (r • x) ⟨le_refl n⟩ =
                  (A.obj.map (hor n (op (n, V.unop)) (le_refl n))) r •
                    (show M.val.obj V from x ⟨le_refl n⟩) := by
                rfl
              rw [hs]
              have h : hor n (op (n, V.unop)) (le_refl n) = 𝟙 _ := by
                apply Quiver.Hom.unop_inj
                apply Prod.hom_ext
                · apply Subsingleton.elim
                · rfl
              rw [h, A.obj.map_id]
              rfl }
        naturality := by intros; rfl } }
  naturality := by intros; rfl

private def coAdj (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}) (n : ℕ) :
    ev₀ J A n ⊣ coFunctor J A n where
  unit := coUnit J A n
  counit := coCounit J A n
  left_triangle_components N := by
    ext V x
    change N.val.map (hor n (op (n, V.unop)) (le_refl n)) x = x
    have h : hor n (op (n, V.unop)) (le_refl n) = 𝟙 _ := by
      apply Quiver.Hom.unop_inj
      apply Prod.hom_ext
      · apply Subsingleton.elim
      · rfl
    rw [h, N.val.map_id]
    rfl
  right_triangle_components M := by
    ext V x
    funext h
    change M.val.map (𝟙 V.unop.2).op (x _) = x h
    rw [op_id, M.val.map_id]
    rfl

private theorem coMate_isIso
    {D : Type (u + 1)} [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{u + 1}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (ψ : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1} J
        (coefficientSequenceTopology J)).obj A ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj
        (((Prod.sectR n D).sheafPushforwardContinuous RingCat.{u + 1} K
          (coefficientSequenceTopology K)).obj B))
    (d : SheafOfModules.pushforward.{u + 1} φ ⋙ ev₀ J A n ≅
      ev₀ K B n ⋙ SheafOfModules.pushforward ψ)
    (hd : ∀ (N : SheafOfModules.{u + 1} B) (U : C)
        (x : ((SheafOfModules.pushforward φ).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op U) x = x) :
    IsIso (mateEquiv (coAdj K B n) (coAdj J A n) d.hom) := by
  let β : coFunctor K B n ⋙ SheafOfModules.pushforward φ ⟶
      SheafOfModules.pushforward ψ ⋙ coFunctor J A n :=
    (mateEquiv (coAdj K B n) (coAdj J A n) d.hom)
  have hb (M) (V : (ℕ × C)ᵒᵖ)
      (x : ((coFunctor K B n ⋙ SheafOfModules.pushforward φ).obj M).val.obj V)
      (h : PLift (n ≤ V.unop.1)) :
      ((β.app M).val.app V x) h = x h := by
    change (((SheafOfModules.pushforward ψ).map ((coAdj K B n).counit.app M)).val.app
      (op V.unop.2)
      ((d.hom.app ((coFunctor K B n).obj M)).val.app (op V.unop.2)
        (((SheafOfModules.pushforward φ).obj ((coFunctor K B n).obj M)).val.map
          (hor n V h.down) x))) = x h
    rw [hd]
    change M.val.map (F.map (𝟙 V.unop.2)).op (x _) = x h
    rw [F.map_id, op_id, M.val.map_id]
    rfl
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  let T := SheafOfModules.forget A ⋙ PresheafOfModules.toPresheaf A.obj
  have ht : IsIso (T.map (β.app M)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro V
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hf : (fun x ↦ (T.map (β.app M)).app V x) = fun x ↦ x := by
      funext x
      funext h
      exact hb M V x h
    constructor
    · intro x y hxy
      have hx := congrFun hf x
      have hy := congrFun hf y
      exact hx.symm.trans (hxy.trans hy)
    · intro y
      exact ⟨y, congrFun hf y⟩
  let := ht
  exact isIso_of_reflects_iso (β.app M) T
private def coFor (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}) (n : ℕ)
    (S : Sheaf J RingCat.{u + 1})
    (h : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1} J
      (coefficientSequenceTopology J)).obj A = S) :
    SheafOfModules.{u + 1} S ⥤ SheafOfModules.{u + 1} A := by
  subst S
  exact coFunctor J A n

private def coForAdj (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}) (n : ℕ)
    (S : Sheaf J RingCat.{u + 1})
    (h : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1} J
      (coefficientSequenceTopology J)).obj A = S) :
    SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom h.symm) ⊣
      coFor J A n S h := by
  subst S
  exact coAdj J A n

private theorem coForMate_isIso
    {D : Type (u + 1)} [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{u + 1}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (S : Sheaf J RingCat.{u + 1}) (T : Sheaf K RingCat.{u + 1})
    (hA : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1} J
      (coefficientSequenceTopology J)).obj A = S)
    (hB : ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{u + 1} K
      (coefficientSequenceTopology K)).obj B = T)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj T)
    (d : SheafOfModules.pushforward.{u + 1} φ ⋙
        SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom hA.symm) ≅
      SheafOfModules.pushforward (F := Prod.sectR n D) (eqToHom hB.symm) ⋙
        SheafOfModules.pushforward ψ)
    (hd : ∀ (N : SheafOfModules.{u + 1} B) (U : C)
        (x : ((SheafOfModules.pushforward φ).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op U) x = x) :
    IsIso (mateEquiv (coForAdj K B n T hB) (coForAdj J A n S hA) d.hom) := by
  subst S
  subst T
  exact coMate_isIso J K F A B n φ ψ d hd

private theorem inverseMate_isIso_of_iterated
    {A B C D : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
    [Category.{u + 1} C] [Category.{u + 1} D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)
    (d : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂)
    [IsIso (mateEquiv adj₄ adj₃ d)] :
    IsIso ((mateEquiv adj₁ adj₂).symm d) := by
  let α := (mateEquiv adj₁ adj₂).symm d
  have h := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ α
  rw [Equiv.apply_symm_apply] at h
  have : IsIso (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α) := by
    rw [← h]
    infer_instance
  exact conjugateEquiv_of_iso (adj₁.comp adj₄) (adj₃.comp adj₂) α

end EvaluationRightAdjoint

attribute [local instance] sliceContinuous

-- The remaining arguments use only these adjunctions and their mate API.
attribute [local irreducible] coFor coForAdj coFunctor coAdj

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Existence of the unit-normalized ordinary pullback evaluation comparison.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-module-eval-g-existence).
Proof: evaluation has an explicit right coextension: at (m,V) it is zero when m < n,
and otherwise M(V), with scalars restricted from level m to level n. Its unit is horizontal
restriction and its counit is evaluation at n. The mate of moduleEvalP under these adjunctions
is identity on section carriers. The iterated-mates identity then makes the inverse mate under
the geometric adjunctions invertible. Its inverse is d; the standard mate/unit identity and
cancellation give the required normalization.
-/
theorem moduleEvalG_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃ d : pull R φ f ⋙ eval R φ X n ≅
        eval R φ Y n ⋙ StrictTower.modulePullback (R n) f,
      ∀ N : Modules R φ Y,
        (eval R φ Y n).map ((moduleAdj R φ f).unit.app N) ≫
          (moduleEvalP R φ f n).hom.app ((pull R φ f).obj N) ≫
          (StrictTower.moduleDirectImage (R n) f).map (d.hom.app N) =
        (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
          (coefficients R X n) (StrictTower.constantRingIso (R n) f)).unit.app
            ((eval R φ Y n).obj N) := by
  let coA (Z : Scheme.{u}) :=
    coForAdj (Scheme.ProEt.topology Z)
      (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Z))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Z) (coefficients R Z)
          (coefficientTransition R φ Z))) n
      (ring.{u + 1, u, u + 1} (Scheme.ProEt.topology Z) (coefficients R Z n))
      (evaluation_ring.{u + 1, u, u + 1} (Scheme.ProEt.topology Z) (coefficients R Z)
        (coefficientTransition R φ Z) n)
  let b := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (Scheme.proEtaleRingDirectImageMap f (coefficients R Y n)
        (coefficients R X n) (StrictTower.constantRingIso (R n) f))
  let : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) :=
    baseChange_continuous f
  have hi : IsIso (mateEquiv (coA X) (coA Y) (moduleEvalP R φ f n).hom) := by
    exact coForMate_isIso _ _ (Scheme.proEtaleBaseChange f)
      _ _ n (ringMap R φ f) _ _
      (evaluation_ring.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
        (coefficients R Y) (coefficientTransition R φ Y) n)
      (evaluation_ring.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients R X) (coefficientTransition R φ X) n)
      b (moduleEvalP R φ f n)
      (moduleEvalP_existsUnique R φ f n).choose_spec.1
  let adj : StrictTower.modulePullback (R n) f ⊣
      StrictTower.moduleDirectImage (R n) f :=
    Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
    (coefficients R X n) (StrictTower.constantRingIso (R n) f)
  have hj : IsIso ((mateEquiv (moduleAdj R φ f) adj).symm
      (moduleEvalP R φ f n).hom) :=
    inverseMate_isIso_of_iterated (moduleAdj R φ f) adj (coA Y) (coA X) _
  let α := ((mateEquiv (moduleAdj R φ f) adj).symm
    (moduleEvalP R φ f n).hom)
  let d := (asIso α).symm
  refine ⟨d, ?_⟩
  intro N
  have h := unit_mateEquiv_symm (moduleAdj R φ f) adj (moduleEvalP R φ f n).hom N
  change (eval R φ Y n).map ((moduleAdj R φ f).unit.app N) ≫
      (moduleEvalP R φ f n).hom.app ((pull R φ f).obj N) =
    adj.unit.app ((eval R φ Y n).obj N) ≫
      (StrictTower.moduleDirectImage (R n) f).map (α.app N) at h
  change (eval R φ Y n).map ((moduleAdj R φ f).unit.app N) ≫
      (moduleEvalP R φ f n).hom.app ((pull R φ f).obj N) ≫
      (StrictTower.moduleDirectImage (R n) f).map (d.hom.app N) =
    adj.unit.app ((eval R φ Y n).obj N)
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
  change adj.unit.app ((eval R φ Y n).obj N) ≫
      (StrictTower.moduleDirectImage (R n) f).map
        ((asIso α).hom.app N ≫ (asIso α).inv.app N) = _
  rw [(asIso α).hom_inv_id_app N]
  exact (congrArg (fun z ↦ adj.unit.app ((eval R φ Y n).obj N) ≫ z)
    ((StrictTower.moduleDirectImage (R n) f).map_id _)).trans (Category.comp_id _)

/-- Uniqueness of the unit-normalized ordinary pullback evaluation comparison.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-module-eval-g-uniqueness).
Proof: apply naturality to the system adjunction unit and use the triangle identity.
The direct-image evaluation comparison is invertible, so the displayed unit equation
cancels its component; the level adjunction hom-equivalence then cancels the remaining
unit and identifies the two natural isomorphisms componentwise.
-/
theorem moduleEvalG_unique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (d e : pull R φ f ⋙ eval R φ X n ≅
      eval R φ Y n ⋙ StrictTower.modulePullback (R n) f)
    (hd : ∀ N : Modules R φ Y,
      (eval R φ Y n).map ((moduleAdj R φ f).unit.app N) ≫
        (moduleEvalP R φ f n).hom.app ((pull R φ f).obj N) ≫
        (StrictTower.moduleDirectImage (R n) f).map (d.hom.app N) =
      (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
        (coefficients R X n) (StrictTower.constantRingIso (R n) f)).unit.app
          ((eval R φ Y n).obj N))
    (he : ∀ N : Modules R φ Y,
      (eval R φ Y n).map ((moduleAdj R φ f).unit.app N) ≫
        (moduleEvalP R φ f n).hom.app ((pull R φ f).obj N) ≫
        (StrictTower.moduleDirectImage (R n) f).map (e.hom.app N) =
      (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
        (coefficients R X n) (StrictTower.constantRingIso (R n) f)).unit.app
          ((eval R φ Y n).obj N)) :
    d = e := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext N
  apply ((Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
    (coefficients R X n) (StrictTower.constantRingIso (R n) f)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hd' := congrArg
    (fun a ↦ a ≫ (StrictTower.moduleDirectImage (R n) f).map (d.inv.app N)) (hd N)
  have he' := congrArg
    (fun a ↦ a ≫ (StrictTower.moduleDirectImage (R n) f).map (e.inv.app N)) (he N)
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hd' he'
  exact hd'.symm.trans he'

theorem moduleEvalG_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : pull R φ f ⋙ eval R φ X n ≅
        eval R φ Y n ⋙ StrictTower.modulePullback (R n) f,
      ∀ N : Modules R φ Y,
        (eval R φ Y n).map ((moduleAdj R φ f).unit.app N) ≫
          (moduleEvalP R φ f n).hom.app ((pull R φ f).obj N) ≫
          (StrictTower.moduleDirectImage (R n) f).map (d.hom.app N) =
        (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
          (coefficients R X n) (StrictTower.constantRingIso (R n) f)).unit.app
            ((eval R φ Y n).obj N) := by
  obtain ⟨d, hd⟩ := moduleEvalG_exists R φ f n
  refine ⟨d, hd, ?_⟩
  intro e he
  exact (moduleEvalG_unique R φ f n d e hd he).symm

/-- The ordinary direct-image comparison is an isomorphism by construction. -/
private theorem moduleEvalP_hom_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (moduleEvalP R φ f n).hom := by
  infer_instance

/-- The normalized ordinary pullback evaluation comparison.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def moduleEvalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pull R φ f ⋙ eval R φ X n ≅
      eval R φ Y n ⋙ StrictTower.modulePullback (R n) f :=
  (moduleEvalG_existsUnique R φ f n).choose

private theorem exact_of_componentwise
    {A B : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    {C D : ℕ → Type (u + 2)} [∀ n, Category.{u + 1} (C n)]
    [∀ n, Category.{u + 1} (D n)] [∀ n, Abelian (C n)] [∀ n, Abelian (D n)]
    (E : ∀ n, B ⥤ D n) (T : ∀ n, A ⥤ C n) (H : ∀ n, C n ⥤ D n)
    [∀ n, (E n).Additive] [∀ n, (T n).Additive] [∀ n, (H n).Additive]
    [∀ n, PreservesFiniteLimits (T n)] [∀ n, PreservesFiniteColimits (T n)]
    [∀ n, PreservesFiniteLimits (H n)] [∀ n, PreservesFiniteColimits (H n)]
    (h : ∀ s : ShortComplex B, s.Exact ↔ ∀ n, (s.map (E n)).Exact)
    (e : ∀ n, F ⋙ E n ≅ T n ⋙ H n) :
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  apply ((Functor.exact_tfae F).out 2 4).mp
  intro s hs
  apply (h (s.map F)).mpr
  intro n
  exact (ShortComplex.exact_iff_of_iso (s.mapNatIso (e n))).mpr
    ((hs.map (T n)).map (H n))

/-- Inverse image is additive and exact on all systems.
Source: Zheng 4.1; Stacks 03EK (blueprint: def-sp-varying-ring-operations).
Proof: the left adjoint is canonically the componentwise abelian inverse image.
Kernels and sheafified cokernels are componentwise; inverse image preserves both.
Addition is inherited from abelian inverse image. No flatness of φ is used. -/
theorem pull_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull R φ f).Additive ∧ PreservesFiniteLimits (pull R φ f) ∧
      PreservesFiniteColimits (pull R φ f) := by
  have : (pull R φ f).Additive := (moduleAdj R φ f).left_adjoint_additive
  refine ⟨inferInstance, ?_⟩
  obtain ⟨A⟩ := semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)
  exact exact_of_componentwise (A := Modules R φ Y) (B := Modules R φ X)
    (C := fun n ↦ StrictTower.Modules (R n) Y)
    (D := fun n ↦ StrictTower.Modules (R n) X)
    (pull R φ f) (eval R φ X) (eval R φ Y)
    (fun n ↦ StrictTower.modulePullback (R n) f)
    A.systems.componentwise (moduleEvalG R φ f)

/-- Open restriction has the extension-by-zero left adjoint.
Source: Stacks 03DI, 09AE (blueprint: def-sp-varying-ring-operations).
Proof: moduleEvalG identifies every level of restriction with evaluation followed by
the single-ring open pullback. Both preserve all limits. The conservative forgetful
functor to presheaves of abelian groups reflects limits, which are pointwise. Thus
restriction preserves all limits. The system category is Grothendieck abelian, so
its small coseparator and the special adjoint functor theorem give a left adjoint. -/
theorem pull_isRightAdjoint {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (pull R φ j).IsRightAdjoint := by
  let : IsGrothendieckAbelian.{u + 1} (Modules R φ X) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
      u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
        (coefficientTransition R φ X))).1
  have hEval (n : ℕ) : (eval R φ X n).IsRightAdjoint :=
    towerEvaluation_isRightAdjoint (C := X.ProEt) (Scheme.ProEt.topology X)
      (coefficients R X)
      (coefficientTransition R φ X) n
  have hH (n : ℕ) : PreservesLimits
      (eval R φ X n ⋙ StrictTower.modulePullback (R n) j) := by
    have := hEval n
    infer_instance
  have : PreservesLimits (pull R φ j) :=
    towerFunctor_preservesLimits (M := Modules R φ X) (C := U.ProEt)
      (Scheme.ProEt.topology U) (coefficients R U)
      (coefficientTransition R φ U) (pull R φ j)
      (fun n ↦ eval R φ X n ⋙ StrictTower.modulePullback (R n) j)
      (moduleEvalG R φ j)
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating.{u + 1}
    (isCoseparator_coseparator (Modules R φ X)) (pull R φ j)

attribute [instance] pull_isRightAdjoint

/-- Additivity needed for the actual exact derived inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) : (pull R φ f).Additive :=
  (pull_exact R φ f).1

/-- Left exactness of the actual inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pull R φ f) := (pull_exact R φ f).2.1

/-- Right exactness of the actual inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pull R φ f) := (pull_exact R φ f).2.2

/-- K-injective resolutions on the actual ringed sequence site.
Source: Stacks 079P; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: the category is modules over systemRing on the small vertical sequence site.
Apply the recorded Grothendieck abelianness and K-injective resolution theorem to
that ringed site. This does not assert that evaluation preserves K-injectives. -/
theorem modules_kInjective (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (Modules R φ X) := by
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u,
        u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
      (coefficientTransition R φ X))).1
  infer_instance

attribute [instance] modules_kInjective

/-- Exact inverse image on the ordinary derived system category.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev G {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived R φ Y ⥤ Derived R φ X :=
  (pull R φ f).mapDerivedCategory

/-- Total right derived direct image, computed on the system category itself.
Source: Stacks 079P (blueprint: def-sp-varying-ring-operations). -/
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived R φ X ⥤ Derived R φ Y :=
  (push R φ f).rightDerivedFunctor

/-- The canonical derived adjunction is induced from the ordinary one.
Source: Stacks 07A6 (blueprint: def-sp-varying-ring-operations). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G R φ f ⊣ P R φ f :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (L := pull R φ f) (R := push R φ f) (moduleAdj R φ f)

private theorem constantMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : CommRingCat.{u + 1}) :
    Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A ≫
      (Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) ≫
      (Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp
          (P := @WeaklyEtale) (Q := ⊤) f g).symm)
        CommRingCat.{u + 1} (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)
          (Scheme.ProEt.topology X)).hom.app (coefficients (fun _ ↦ A) X 0) =
      Scheme.proEtaleConstantDirectImageMap (f ≫ g) CommRingCat.{u + 1} A := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Z.ProEtᵒᵖ).obj A) _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
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
      ((Scheme.proEtaleBaseChange g).op.obj U) = _ at hfU
  change ((toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
      ((Scheme.proEtaleBaseChange g).op.obj U) ≫
    (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
      ((Scheme.proEtaleBaseChange g).op.obj U)) ≫
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app
            U.unop).op = _
  rw [hfU]
  erw [Equiv.apply_symm_apply]
  have hn := (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
  change 𝟙 A ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  exact hn.symm

/-- Ordinary direct-image composition is fixed on every section and coefficient index.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations).
Proof: restriction along the canonical fibre-product pasting isomorphism is linear,
natural in test objects, and compatible with every coefficient transition. Its
inverse is restriction along the inverse isomorphism. Sections determine uniqueness. -/
theorem modulePComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! d : push R φ f ⋙ push R φ g ≅ push R φ (f ≫ g),
      ∀ (N : Modules R φ X) (n : ℕ) (U : Z.ProEt)
        (x : ((push R φ f ⋙ push R φ g).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op (n, U)) x =
          N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
  have := Functor.isContinuous_comp (baseChange g) (baseChange f)
    (coefficientSequenceTopology (Scheme.ProEt.topology Z))
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
  let e : baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
    NatIso.prod (Iso.refl (𝟭 ℕ)) (MorphismProperty.Over.pullbackComp f g)
  let a : sequenceRing R φ Z ⟶
      ((baseChange g ⋙ baseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Z))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj (sequenceRing R φ X) :=
    ringMap R φ g ≫ ((baseChange g).sheafPushforwardContinuous RingCat.{u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology Z))
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))).map (ringMap R φ f)
  have h : a ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).app (sequenceRing R φ X) =
      ringMap R φ (f ≫ g) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change ringMapApp R g U ≫
      ringMapApp R f (op (U.unop.1, (Scheme.proEtaleBaseChange g).obj U.unop.2)) ≫
        (sequenceRing R φ X).obj.map
          (Prod.mkHom (𝟙 U.unop.1)
            ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop.2)).op = _
    rw [sequenceRing_map_vertical]
    exact (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).congr_map
      (congrArg (fun t ↦ t.hom.app (op U.unop.2))
        (constantMap_comp f g (R U.unop.1)))
  let d : push R φ f ⋙ push R φ g ≅ push R φ (f ≫ g) :=
    SheafOfModules.pushforwardComp (ringMap R φ g) (ringMap R φ f) ≪≫
      SheafOfModules.pushforwardNatIso a e ≪≫ SheafOfModules.pushforwardCongr h
  have hd : ∀ (N : Modules R φ X) (n : ℕ) (U : Z.ProEt)
      (x : ((push R φ f ⋙ push R φ g).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op (n, U)) x =
        N.val.map (Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
    intros
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (hd' N U.unop.1 U.unop.2 x).trans (hd N U.unop.1 U.unop.2 x).symm

/-- The section-normalized compositor for ordinary direct image.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def modulePComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (modulePComp_existsUnique R φ f g).choose

/-- Inverse-image composition is its unit-preserving conjugate.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def moduleGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull R φ (f ≫ g) ≅ pull R φ g ⋙ pull R φ f :=
  (Adjunction.leftAdjointCompIso
    (F₀₁ := pull R φ g) (F₁₂ := pull R φ f) (F₀₂ := pull R φ (f ≫ g))
    (G₁₀ := push R φ g) (G₂₁ := push R φ f) (G₂₀ := push R φ (f ≫ g))
    (moduleAdj R φ g) (moduleAdj R φ f)
    (moduleAdj R φ (f ≫ g)) (modulePComp R φ f g)).symm

/-- Derived inverse-image composition is localized from the actual system comparison.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def gComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G R φ (f ≫ g) ≅ G R φ g ⋙ G R φ f :=
  Functor.mapDerivedCategoryNatIso (moduleGComp R φ f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (pull R φ g) (pull R φ f)).symm

/-- Proper direct-image composition is the conjugate of inverse-image composition.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P R φ f ⋙ P R φ g ≅ P R φ (f ≫ g) :=
  conjugateIsoEquiv (L₁ := G R φ g ⋙ G R φ f) (R₁ := P R φ f ⋙ P R φ g)
    (L₂ := G R φ (f ≫ g)) (R₂ := P R φ (f ≫ g))
    ((adj R φ g).comp (adj R φ f)) (adj R φ (f ≫ g)) (gComp R φ f g)

/-- The identity comparison for ordinary direct image is the pullback graph map.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations).
Proof: restriction along the graph of the identity base change is a linear isomorphism
at every index. The inverse graph gives its inverse. These maps commute with the
semilinear transitions, and the section formula determines them uniquely. -/
theorem modulePId_existsUnique (X : Scheme.{u}) :
    ∃! d : push R φ (𝟙 X) ≅ 𝟭 (Modules R φ X),
      ∀ (N : Modules R φ X) (n : ℕ) (U : X.ProEt)
        (x : ((push R φ (𝟙 X)).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op (n, U)) x =
          N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U)).op x := by
  let e : baseChange (𝟙 X) ≅ 𝟭 (ℕ × X.ProEt) :=
    NatIso.prod (Iso.refl (𝟭 ℕ)) (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X)
  have h : ringMap R φ (𝟙 X) ≫
      (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).app (sequenceRing R φ X) =
      𝟙 (sequenceRing R φ X) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hc : Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1}
          (R U.unop.1) ≫
        (Functor.sheafPushforwardContinuousId'
          (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
            (Scheme.ProEt.topology X)).hom.app (coefficients R X U.unop.1) =
        𝟙 (coefficients R X U.unop.1) := by
      apply ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv
         ((Functor.const X.ProEtᵒᵖ).obj (R U.unop.1)) _).injective
      rw [Adjunction.homEquiv_naturality_right]
      simp only [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
      apply NatTrans.ext
      funext V
      change (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (R U.unop.1))).app
          ((Scheme.proEtaleBaseChange (𝟙 X)).op.obj V) ≫
          (coefficients R X U.unop.1).obj.map
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op = _
      have hn := (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (R U.unop.1))).naturality
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op
      change 𝟙 (R U.unop.1) ≫ _ = _ at hn
      rw [Category.id_comp] at hn
      rw [Adjunction.homEquiv_unit]
      change _ = (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (R U.unop.1))).app V ≫ 𝟙 _
      rw [Category.comp_id]
      exact hn.symm
    change ringMapApp R (𝟙 X) U ≫
      (sequenceRing R φ X).obj.map
        (Prod.mkHom (𝟙 U.unop.1)
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U.unop.2)).op = _
    rw [sequenceRing_map_vertical]
    exact (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).congr_map
      (congrArg (fun t ↦ t.hom.app (op U.unop.2)) hc)
  let d : push R φ (𝟙 X) ≅ 𝟭 (Modules R φ X) :=
    SheafOfModules.pushforwardNatIso (ringMap R φ (𝟙 X)) e.symm ≪≫
      SheafOfModules.pushforwardCongr h ≪≫ SheafOfModules.pushforwardId _
  have hd : ∀ (N : Modules R φ X) (n : ℕ) (U : X.ProEt)
      (x : ((push R φ (𝟙 X)).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op (n, U)) x =
        N.val.map (Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U)).op x := by
    intros
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (hd' N U.unop.1 U.unop.2 x).trans (hd N U.unop.1 U.unop.2 x).symm

/-- The uniquely normalized ordinary identity comparison.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def modulePId (X : Scheme.{u}) := (modulePId_existsUnique R φ X).choose

/-- The inverse-image identity is localized from the adjoint identity comparison.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def gId (X : Scheme.{u}) : G R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Functor.mapDerivedCategoryNatIso
    (Adjunction.leftAdjointIdIso (F := pull R φ (𝟙 X)) (G := push R φ (𝟙 X))
      (moduleAdj R φ (𝟙 X)) (modulePId R φ X)) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The right-adjoint identity is fixed by the same unit normalization.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def pId (X : Scheme.{u}) : P R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  (conjugateIsoEquiv (L₁ := 𝟭 (Derived R φ X)) (R₁ := 𝟭 (Derived R φ X))
    (L₂ := G R φ (𝟙 X)) (R₂ := P R φ (𝟙 X))
    Adjunction.id (adj R φ (𝟙 X)) (gId R φ X)).symm

/-- Open extension chosen by the localized module universal property.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
abbrev extension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (pull R φ j).leftAdjoint

/-- The actual ordinary open-extension adjunction.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def moduleJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension R φ j ⊣ pull R φ j := Adjunction.ofIsRightAdjoint _

section OpenRestrictionModel
set_option synthInstance.maxSize 128
open CategoryTheory.Functor AlgebraicGeometry.Scheme
private def prodAdj {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) : (𝟭 ℕ).prod F ⊣ (𝟭 ℕ).prod G where
  unit.app X := Prod.mkHom (𝟙 X.1) (a.unit.app X.2)
  unit.naturality := by
    intro X Y f
    apply Prod.hom_ext
    · apply Subsingleton.elim
    · exact a.unit.naturality f.2
  counit.app X := Prod.mkHom (𝟙 X.1) (a.counit.app X.2)
  counit.naturality := by
    intro X Y f
    apply Prod.hom_ext
    · apply Subsingleton.elim
    · exact a.counit.naturality f.2
  left_triangle_components X := by
    apply Prod.hom_ext
    · apply Subsingleton.elim
    · exact a.left_triangle_components X.2
  right_triangle_components X := by
    apply Prod.hom_ext
    · apply Subsingleton.elim
    · exact a.right_triangle_components X.2

private theorem prodContinuous {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
    [F.IsContinuous J K] :
    ((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K) := by
  constructor
  intro G
  apply sequence_isSheaf_of_slices J
  intro n
  have := evaluationContinuous.{u + 1, u, u + 1} K n
  let H := ((Prod.sectR n D).sheafPushforwardContinuous (Type (u + 1)) K
    (coefficientSequenceTopology K)).obj G
  change Presieve.IsSheaf J (F.op ⋙ H.obj)
  exact Functor.IsContinuous.op_comp_isSheaf_of_types H

private def openMap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    U.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

private local instance openMapContinuous {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openMap j).IsContinuous (ProEt.topology U) (ProEt.topology X) :=
  ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

private def openAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openMap j ⊣ proEtaleBaseChange j :=
  MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial

private local instance prodOpenContinuous {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((𝟭 ℕ).prod (openMap j)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  exact prodContinuous _ _ _
private theorem iso_inverse_transpose
    {A B : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
    {L L' : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) (b : L' ⊣ R)
    {M : A} {N : B} (f : M ⟶ R.obj N) [IsIso ((b.homEquiv M N).symm f)] :
    IsIso ((a.homEquiv M N).symm f) := by
  have h : (a.homEquiv M N).symm f =
      (a.leftAdjointUniq b).hom.app M ≫ (b.homEquiv M N).symm f := by
    apply (a.homEquiv M N).injective
    rw [Equiv.apply_symm_apply, a.homEquiv_naturality_right,
      a.homEquiv_leftAdjointUniq_hom_app]
    exact (b.homEquiv M N).apply_symm_apply f |>.symm
  rw [h]
  infer_instance

private def openConstantTranspose {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : CommRingCat.{u + 1}) :=
  (((openAdj j).sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U) (ProEt.topology X)).homEquiv _ _).symm
      (proEtaleConstantDirectImageMap j CommRingCat.{u + 1} B)

private theorem openConstantAdjoint_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : CommRingCat.{u + 1}) :
    IsIso ((((openAdj j).sheafPushforwardContinuous
      (E := CommRingCat.{u + 1}) (ProEt.topology U) (ProEt.topology X)).homEquiv _ _).symm
      (proEtaleConstantDirectImageMap j CommRingCat.{u + 1} B)) := by
  have : IsIso (((proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _).symm
      (proEtaleConstantDirectImageMap j CommRingCat.{u + 1} B)) := by
    change IsIso (StrictTower.constantRingIso B j).hom
    infer_instance
  exact iso_inverse_transpose _ (proEtaleSheafAdjunction j CommRingCat.{u + 1}) _

open AlgebraicGeometry.ProEtale.VaryingRing
private abbrev seqRing (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n) (X : Scheme.{u}) :=
  ring.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology X))
    (systemRing.{u + 1, u, u + 1} (ProEt.topology X) (coefficients R X)
      (coefficientTransition R φ X))

private def openRingTranspose (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n) {U X :
  Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (((𝟭 ℕ).prod (openMap j)).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology (ProEt.topology X))).obj (seqRing R φ X) ⟶
    seqRing R φ U :=
  (((prodAdj (openAdj j)).sheafPushforwardContinuous (E := RingCat.{u + 1})
    (coefficientSequenceTopology (ProEt.topology U))
    (coefficientSequenceTopology (ProEt.topology X))).homEquiv _ _).symm (ringMap R φ j)

private theorem openRingTranspose_app (R : ℕ → CommRingCat.{u + 1})
    (φ : ∀ n, R (n + 1) ⟶ R n) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (V : (ℕ × U.ProEt)ᵒᵖ) :
    (openRingTranspose R φ j).hom.app V =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((openConstantTranspose j (R V.unop.1)).hom.app (op V.unop.2)) := by
  change _ = (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((proEtaleConstantDirectImageMap j CommRingCat.{u + 1} (R V.unop.1)).hom.app
      (op ((openMap j).obj V.unop.2)) ≫
    (coefficients R U V.unop.1).obj.map ((openAdj j).unit.app V.unop.2).op)
  simp only [openRingTranspose, Adjunction.homEquiv_counit]
  change ringMapApp R j (op (V.unop.1, (openMap j).obj V.unop.2)) ≫
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (((rings.{u + 1, u, u + 1} (ProEt.topology U) (coefficients R U)
        (coefficientTransition R φ U)).map (𝟙 (op V.unop.1))).hom.app
          (op ((proEtaleBaseChange j).obj ((openMap j).obj V.unop.2))) ≫
        (coefficients R U V.unop.1).obj.map ((openAdj j).unit.app V.unop.2).op) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

private theorem openRingTranspose_isIso (R : ℕ → CommRingCat.{u + 1})
    (φ : ∀ n, R (n + 1) ⟶ R n) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (openRingTranspose R φ j) := by
  have h (V : (ℕ × U.ProEt)ᵒᵖ) : IsIso ((openRingTranspose R φ j).hom.app V) := by
    have : IsIso (openConstantTranspose j (R V.unop.1)) :=
      openConstantAdjoint_isIso j (R V.unop.1)
    rw [openRingTranspose_app]
    infer_instance
  have : IsIso ((sheafToPresheaf _ RingCat.{u + 1}).map (openRingTranspose R φ j)) :=
    (NatTrans.isIso_iff_isIso_app _).mpr h
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ RingCat.{u + 1})

attribute [local instance] openRingTranspose_isIso

private def moduleAdjOfSiteAdj
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K] [G.IsContinuous K J]
    (a : F ⊣ G) {S : Sheaf J RingCat.{u + 1}} {T : Sheaf K RingCat.{u + 1}}
    (ψ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).obj S)
    [IsIso (((a.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K).homEquiv T S).symm ψ)] :
    SheafOfModules.pushforward.{u + 1}
      (inv (((a.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K).homEquiv T S).symm ψ)) ⊣
      SheafOfModules.pushforward.{u + 1} ψ := by
  let b := a.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K
  let d := (b.homEquiv T S).symm ψ
  refine SheafOfModules.pushforwardPushforwardAdj a (inv d) ψ ?_ ?_
  · have ht : b.unit.app T ≫ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).map d = ψ :=
      (b.homEquiv T S).apply_symm_apply ψ
    have h : b.unit.app T =
        ψ ≫ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).map (inv d) := by
      rw [← ht, Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
        CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).symm
    exact congrArg (fun t ↦ t.hom) h
  · change (inv d ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map ψ ≫
      b.counit.app S).hom = (𝟙 S : S ⟶ S).hom
    change (inv d ≫ d).hom = (𝟙 S : S ⟶ S).hom
    rw [IsIso.inv_hom_id]

private def openPullAdj (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n) {U X : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j] :
    SheafOfModules.pushforward.{u + 1} (F := (𝟭 ℕ).prod (openMap j))
      (S := seqRing R φ U) (R := seqRing R φ X) (inv (openRingTranspose R φ j)) ⊣ push R φ j := by
  have : IsIso ((((prodAdj (openAdj j)).sheafPushforwardContinuous
      (E := RingCat.{u + 1}) (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology (ProEt.topology X))).homEquiv _ _).symm
        (ringMap R φ j)) := openRingTranspose_isIso R φ j
  exact moduleAdjOfSiteAdj _ _ (prodAdj (openAdj j)) (ringMap R φ j)

private def moduleAdjOfSiteAdj'
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K] [G.IsContinuous K J]
    (a : F ⊣ G) {S : Sheaf J RingCat.{u + 1}} {T : Sheaf K RingCat.{u + 1}}
    (ψ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).obj S)
    (d : (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj T ⟶ S) [IsIso d]
    (hd : d = ((a.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K).homEquiv T S).symm ψ) :
    SheafOfModules.pushforward.{u + 1} (inv d) ⊣ SheafOfModules.pushforward.{u + 1} ψ := by
  let b := a.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K
  refine SheafOfModules.pushforwardPushforwardAdj a (inv d) ψ ?_ ?_
  · have ht : b.unit.app T ≫ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).map d = ψ := by
      rw [hd]
      exact (b.homEquiv T S).apply_symm_apply ψ
    have h : b.unit.app T =
        ψ ≫ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).map (inv d) := by
      rw [← ht, Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
        CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).symm
    exact congrArg (fun t ↦ t.hom) h
  · change (inv d ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map ψ ≫
      b.counit.app S).hom = (𝟙 S : S ⟶ S).hom
    have ht : (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map ψ ≫
        b.counit.app S = d := hd.symm
    rw [ht, IsIso.inv_hom_id]

private def openLevelTranspose {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : CommRingCat.{u + 1}) :
    ((openMap j).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X)).obj
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj B)) ⟶
    (sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).obj B) :=
  ⟨Functor.whiskerRight (openConstantTranspose j B).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private local instance openLevelTranspose_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : CommRingCat.{u + 1}) : IsIso (openLevelTranspose j B) := by
  have : IsIso (openConstantTranspose j B) := openConstantAdjoint_isIso j B
  change IsIso ((sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (openConstantTranspose j B))
  infer_instance

attribute [local instance] openLevelTranspose_isIso

private def openLevelAdj (R : ℕ → CommRingCat.{u + 1}) {U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j] (n : ℕ) :
    SheafOfModules.pushforward.{u + 1} (@inv _ _ _ _ (openLevelTranspose j (R n))
      (openLevelTranspose_isIso j (R n))) ⊣
      StrictTower.moduleDirectImage (R n) j := by
  let b : (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients R X n) ⟶
      ((proEtaleBaseChange j).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology U)).obj
        ((sheafCompose (ProEt.topology U)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients R U n)) :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap j (coefficients R X n) (coefficients R U n)
        (StrictTower.constantRingIso (R n) j)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have := openLevelTranspose_isIso j (R n)
  exact moduleAdjOfSiteAdj' (ProEt.topology U) (ProEt.topology X) (openAdj j) b
    (openLevelTranspose j (R n)) (by
      have hb : proEtaleRingDirectImageMap j (coefficients R X n)
          (coefficients R U n) (StrictTower.constantRingIso (R n) j) =
          proEtaleConstantDirectImageMap j CommRingCat.{u + 1} (R n) :=
        ((proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
      dsimp only [openLevelTranspose, openConstantTranspose]
      simp only [Adjunction.homEquiv_counit]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          ((proEtaleConstantDirectImageMap j CommRingCat.{u + 1} (R n)).hom.app
            (op ((openMap j).obj V.unop)) ≫
            (coefficients R U n).obj.map ((openAdj j).unit.app V.unop).op) =
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          ((proEtaleRingDirectImageMap j (coefficients R X n) (coefficients R U n)
            (StrictTower.constantRingIso (R n) j)).hom.app
              (op ((openMap j).obj V.unop)) ≫
            (coefficients R U n).obj.map ((openAdj j).unit.app V.unop).op)
      rw [hb])

private theorem openTranspose_inv_app
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (V : U.ProEtᵒᵖ) :
    (inv (openRingTranspose R φ j)).hom.app (op (n, V.unop)) =
      (@inv _ _ _ _ (openLevelTranspose j (R n))
        (openLevelTranspose_isIso j (R n))).hom.app V := by
  simp only [ObjectProperty.hom_inv, NatIso.isIso_inv_app, openRingTranspose_app,
    openLevelTranspose]
  rfl

-- Specialize the cached section-normalization statement rather than re-elaborating
-- the two transported module carriers in its predicate.
private theorem openEval_exists
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    type_of% (towerPushforwardEvaluation
      (ProEt.topology U) (ProEt.topology X) (openMap j) (coefficients R U)
      (coefficientTransition R φ U) (coefficients R X) (coefficientTransition R φ X)
      n (inv (openRingTranspose R φ j)) (@inv _ _ _ _ (openLevelTranspose j (R n))
        (openLevelTranspose_isIso j (R n))) (openTranspose_inv_app R φ j n)) :=
  towerPushforwardEvaluation
      (ProEt.topology U) (ProEt.topology X) (openMap j) (coefficients R U)
      (coefficientTransition R φ U) (coefficients R X) (coefficientTransition R φ X)
      n (inv (openRingTranspose R φ j)) (@inv _ _ _ _ (openLevelTranspose j (R n))
        (openLevelTranspose_isIso j (R n))) (openTranspose_inv_app R φ j n)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem extensionEvaluation_exists
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    Nonempty (extension R φ j ⋙ eval R φ X n ≅
      eval R φ U n ⋙ StrictTower.moduleJ (R n) j) := by
  let coA (Z : Scheme.{u}) :=
    coForAdj (ProEt.topology Z)
      (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology Z))
        (systemRing.{u + 1, u, u + 1} (ProEt.topology Z) (coefficients R Z)
          (coefficientTransition R φ Z))) n
      (ring.{u + 1, u, u + 1} (ProEt.topology Z) (coefficients R Z n))
      (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology Z) (coefficients R Z)
        (coefficientTransition R φ Z) n)
  let d := (openEval_exists R φ j n).choose
  let ψ := @inv _ _ _ _ (openLevelTranspose j (R n)) (openLevelTranspose_isIso j (R n))
  let : ((𝟭 ℕ).prod (openMap j)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology (ProEt.topology X)) := prodOpenContinuous j
  have : IsIso (mateEquiv (coA X) (coA U) d.hom) := by
    exact coForMate_isIso _ _ (openMap j) _ _ n (inv (openRingTranspose R φ j)) _ _
      (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology U)
        (coefficients R U) (coefficientTransition R φ U) n)
      (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology X)
        (coefficients R X) (coefficientTransition R φ X) n)
      ψ d (openEval_exists R φ j n).choose_spec.1
  let e := (moduleAdj R φ j).leftAdjointUniq (openPullAdj R φ j)
  let l := proEtaleRingModuleAdjunction j (coefficients R X n)
    (coefficients R U n) (StrictTower.constantRingIso (R n) j)
  let e' := l.leftAdjointUniq (openLevelAdj R j n)
  let β := isoWhiskerLeft (coFor (ProEt.topology X) (seqRing R φ X) n
      (ring.{u + 1, u, u + 1} (ProEt.topology X) (coefficients R X n))
      (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology X)
        (coefficients R X) (coefficientTransition R φ X) n)) e ≪≫
    asIso (mateEquiv (coA X) (coA U) d.hom) ≪≫
      isoWhiskerRight e'.symm (coFor (ProEt.topology U) (seqRing R φ U) n
        (ring.{u + 1, u, u + 1} (ProEt.topology U) (coefficients R U n))
        (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology U)
          (coefficients R U) (coefficientTransition R φ U) n))
  exact ⟨((conjugateIsoEquiv ((moduleJAdj R φ j).comp (coA X))
    ((coA U).comp (StrictTower.moduleJAdj (R n) j))).symm β).symm⟩

end OpenRestrictionModel

section OpenEvaluationMates
set_option synthInstance.maxSize 128
open CategoryTheory.Functor AlgebraicGeometry.Scheme
attribute [local instance] openMapContinuous prodOpenContinuous prodBaseContinuous
  openRingTranspose_isIso openLevelTranspose_isIso
private local instance fixedEvalContinuous {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) :=
  SemilinearSections.evaluationContinuous.{u + 1, u, u + 1} J n

private theorem openPullUnit
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Modules R φ X) (V : X.ProEt) (n : ℕ)
    (x : M.val.obj (op (n, V))) :
    ((openPullAdj R φ j).unit.app M).val.app (op (n, V)) x =
      M.val.map (Prod.mkHom (𝟙 n) ((openAdj j).counit.app V)).op x := by rfl

private theorem openLevelUnit
    (R : ℕ → CommRingCat.{u + 1}) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) (M : StrictTower.Modules (R n) X) (V : X.ProEt)
    (x : M.val.obj (op V)) :
    ((openLevelAdj R j n).unit.app M).val.app (op V) x =
      M.val.map ((openAdj j).counit.app V).op x := by rfl

private theorem sheafModule_comp_apply
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A : Sheaf J RingCat.{u + 1}} {M N P : SheafOfModules.{u + 1} A}
    (f : M ⟶ N) (g : N ⟶ P) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((f ≫ g).val.app V) x = (g.val.app V) ((f.val.app V) x) := rfl

attribute [local irreducible] openPullAdj openLevelAdj constantSheaf presheafToSheaf
  systemRing rings

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem openEval_unit
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (M : Modules R φ X) :
    (eval R φ X n).map ((openPullAdj R φ j).unit.app M) ≫
      (moduleEvalP R φ j n).hom.app
        ((SheafOfModules.pushforward.{u + 1} (F := (𝟭 ℕ).prod (openMap j))
      (S := seqRing R φ U) (R := seqRing R φ X) (inv (openRingTranspose R φ j))).obj M) ≫
      (StrictTower.moduleDirectImage (R n) j).map
        ((openEval_exists R φ j n).choose.hom.app M) =
      (openLevelAdj R j n).unit.app ((eval R φ X n).obj M) := by
  ext V x
  rw [sheafModule_comp_apply, sheafModule_comp_apply]
  let y := (((openPullAdj R φ j).unit.app M).val.app (op (n, V.unop))) x
  let z := (((moduleEvalP R φ j n).hom.app
    ((SheafOfModules.pushforward.{u + 1} (F := (𝟭 ℕ).prod (openMap j))
      (S := seqRing R φ U) (R := seqRing R φ X) (inv (openRingTranspose R φ j))).obj M)).val.app V)
        y
  have hq := (openEval_exists R φ j n).choose_spec.1 M
    ((proEtaleBaseChange j).obj V.unop) z
  have hp := (moduleEvalP_existsUnique R φ j n).choose_spec.1
    ((SheafOfModules.pushforward.{u + 1} (F := (𝟭 ℕ).prod (openMap j))
      (S := seqRing R φ U) (R := seqRing R φ X) (inv (openRingTranspose R φ j))).obj M) V.unop y
  exact hq.trans (hp.trans ((openPullUnit R φ j M V.unop n x).trans
    (openLevelUnit R j n ((eval R φ X n).obj M) V.unop x).symm))

private theorem transportedUnit
    {A B C D : Type u} [Category A] [Category B] [Category C] [Category D]
    {F Q : A ⥤ B} {P : B ⥤ A} {F' Q' : C ⥤ D} {P' : D ⥤ C}
    (a : F ⊣ P) (qa : Q ⊣ P) (b : F' ⊣ P') (qb : Q' ⊣ P')
    (E : A ⥤ C) (E' : B ⥤ D) (d : P ⋙ E ≅ E' ⋙ P')
    (q : Q ⋙ E' ≅ E ⋙ Q')
    (hq : ∀ N, E.map (qa.unit.app N) ≫ d.hom.app (Q.obj N) ≫
      P'.map (q.hom.app N) = qb.unit.app (E.obj N)) (N : A) :
    E.map (a.unit.app N) ≫ d.hom.app (F.obj N) ≫
      P'.map ((isoWhiskerRight (a.leftAdjointUniq qa) E' ≪≫ q ≪≫
        isoWhiskerLeft E (b.leftAdjointUniq qb).symm).hom.app N) =
      b.unit.app (E.obj N) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp]
  have hn := d.hom.naturality ((a.leftAdjointUniq qa).hom.app N)
  change E.map (P.map ((a.leftAdjointUniq qa).hom.app N)) ≫ d.hom.app (Q.obj N) =
    d.hom.app (F.obj N) ≫ P'.map (E'.map ((a.leftAdjointUniq qa).hom.app N)) at hn
  rw [← reassoc_of% hn]
  change E.map (a.unit.app N) ≫ E.map (P.map ((a.leftAdjointUniq qa).hom.app N)) ≫
    d.hom.app (Q.obj N) ≫ P'.map (q.hom.app N) ≫
      P'.map ((b.leftAdjointUniq qb).inv.app (E.obj N)) = _
  rw [← E.map_comp_assoc, a.unit_leftAdjointUniq_hom_app qa]
  rw [reassoc_of% (hq N)]
  rw [← b.unit_leftAdjointUniq_hom_app qb]
  simp only [Category.assoc, ← P'.map_comp, Iso.hom_inv_id_app, P'.map_id]
  exact Category.comp_id _

private theorem inverseMateIsoOfUnit
    {A B C D : Type u} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {P : B ⥤ A} {F' : C ⥤ D} {P' : D ⥤ C}
    (a : F ⊣ P) (b : F' ⊣ P') (E : A ⥤ C) (E' : B ⥤ D)
    (d : P ⋙ E ⟶ E' ⋙ P') (q : F ⋙ E' ≅ E ⋙ F')
    (hq : ∀ N, E.map (a.unit.app N) ≫ d.app (F.obj N) ≫
      P'.map (q.hom.app N) = b.unit.app (E.obj N)) :
    IsIso ((mateEquiv a b).symm d) := by
  have h : ((mateEquiv a b).symm d) = q.inv := by
    apply NatTrans.ext
    funext N
    apply (b.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have hu : E.map (a.unit.app N) ≫ d.app (F.obj N) =
        b.unit.app (E.obj N) ≫ P'.map (((mateEquiv a b).symm d).app N) :=
      unit_mateEquiv_symm a b d N
    rw [← hu]
    apply (cancel_mono (P'.map (q.hom.app N))).mp
    simp only [Category.assoc]
    rw [← P'.map_comp, Iso.inv_hom_id_app]
    exact (hq N).trans ((congrArg (fun z ↦ b.unit.app (E.obj N) ≫ z)
      (P'.map_id _)).trans (Category.comp_id _)).symm
  rw [h]
  infer_instance

private theorem inverseMateIsoOfOtherAdj
    {A B C D : Type u} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {P : B ⥤ A} {F' : C ⥤ D} {P' : D ⥤ C}
    (a qa : F ⊣ P) (b qb : F' ⊣ P') (E : A ⥤ C) (E' : B ⥤ D)
    (d : P ⋙ E ≅ E' ⋙ P')
    [IsIso ((mateEquiv qa qb).symm d.hom)] :
    IsIso ((mateEquiv a b).symm d.hom) := by
  let α := ((mateEquiv qa qb).symm d.hom)
  let q := (asIso α).symm
  have hq (N : A) : E.map (qa.unit.app N) ≫ d.hom.app (F.obj N) ≫
      P'.map (q.hom.app N) = qb.unit.app (E.obj N) := by
    rw [← Category.assoc, unit_mateEquiv_symm qa qb d.hom N, Category.assoc,
      ← P'.map_comp]
    change qb.unit.app (E.obj N) ≫ P'.map
      ((asIso α).hom.app N ≫ (asIso α).inv.app N) = _
    rw [(asIso α).hom_inv_id_app N]
    exact (congrArg (fun z ↦ qb.unit.app (E.obj N) ≫ z) (P'.map_id _)).trans
      (Category.comp_id _)
  exact inverseMateIsoOfUnit a b E E' d.hom
    (isoWhiskerRight (a.leftAdjointUniq qa) E' ≪≫ q ≪≫
      isoWhiskerLeft E (b.leftAdjointUniq qb).symm)
    (transportedUnit a qa b qb E E' d q hq)

private theorem mateWhiskerIso
    {A B C D : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
    [Category.{u + 1} C] [Category.{u + 1} D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (d : G ⋙ L₂ ≅ L₁ ⋙ H)
    (σ : G' ≅ G) (τ : H ≅ H') [IsIso (mateEquiv a b d.hom)] :
    IsIso (mateEquiv a b
      (isoWhiskerRight σ L₂ ≪≫ d ≪≫ isoWhiskerLeft L₁ τ).hom) := by
  have hd : (isoWhiskerRight σ L₂ ≪≫ d ≪≫ isoWhiskerLeft L₁ τ).hom =
      (((TwoSquare.mk _ _ _ _ d.hom).whiskerTop σ.hom).whiskerBottom τ.hom) := by
    ext X
    simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
      TwoSquare.whiskerTop, TwoSquare.whiskerBottom, Category.assoc]
  rw [hd]
  rw [mateEquiv_whiskerTop_whiskerBottom]
  dsimp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft]
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryOpenMateIso
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    IsIso ((mateEquiv (moduleJAdj R φ j) (StrictTower.moduleJAdj (R n) j)).symm
      (moduleEvalG R φ j n).hom) := by
  let coA (Z : Scheme.{u}) :=
    coForAdj (ProEt.topology Z)
      (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology Z))
        (systemRing.{u + 1, u, u + 1} (ProEt.topology Z) (coefficients R Z)
          (coefficientTransition R φ Z))) n
      (ring.{u + 1, u, u + 1} (ProEt.topology Z) (coefficients R Z n))
      (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology Z) (coefficients R Z)
        (coefficientTransition R φ Z) n)
  let d := (openEval_exists R φ j n).choose
  let ψ := @inv _ _ _ _ (openLevelTranspose j (R n)) (openLevelTranspose_isIso j (R n))
  let : ((𝟭 ℕ).prod (openMap j)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology (ProEt.topology X)) := prodOpenContinuous j
  have : IsIso (mateEquiv (coA X) (coA U) d.hom) := by
    exact coForMate_isIso _ _ (openMap j) _ _ n (inv (openRingTranspose R φ j)) _ _
      (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology U)
        (coefficients R U) (coefficientTransition R φ U) n)
      (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology X)
        (coefficients R X) (coefficientTransition R φ X) n)
      ψ d (openEval_exists R φ j n).choose_spec.1
  let l := proEtaleRingModuleAdjunction j (coefficients R X n)
    (coefficients R U n) (StrictTower.constantRingIso (R n) j)
  let e := (moduleAdj R φ j).leftAdjointUniq (openPullAdj R φ j)
  let e' := l.leftAdjointUniq (openLevelAdj R j n)
  let q := isoWhiskerRight e (eval R φ U n) ≪≫ d ≪≫
    isoWhiskerLeft (eval R φ X n) e'.symm
  have hq : q = moduleEvalG R φ j n := by
    apply moduleEvalG_unique R φ j n
    · exact transportedUnit (moduleAdj R φ j) (openPullAdj R φ j) l
        (openLevelAdj R j n) (eval R φ X n) (eval R φ U n)
        (moduleEvalP R φ j n) d (openEval_unit R φ j n)
    · exact (moduleEvalG_existsUnique R φ j n).choose_spec.1
  have : IsIso (mateEquiv (coA X) (coA U) q.hom) :=
    mateWhiskerIso (coA X) (coA U) d e e'.symm
  have : IsIso (mateEquiv (coA X) (coA U) (moduleEvalG R φ j n).hom) := by
    exact hq ▸ (inferInstance : IsIso (mateEquiv (coA X) (coA U) q.hom))
  exact inverseMate_isIso_of_iterated (moduleJAdj R φ j) (StrictTower.moduleJAdj (R n) j)
    (coA U) (coA X) (moduleEvalG R φ j n).hom

end OpenEvaluationMates

attribute [local instance] fixedEvalContinuous

/-- Exactness of extension by zero, including the empty open.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations).
Proof: the open-site map/base-change adjunction presents pullback as continuous
module pushforward along the inverse transpose of the coefficient map. Evaluation
commutes with this presentation and its right coextension. Adjoint uniqueness and
conjugation give coefficientwise comparison with the existing single-ring extension
by zero. Its exactness and the componentwise short-complex criterion give the claim. -/
theorem extension_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension R φ j).Additive ∧ PreservesFiniteLimits (extension R φ j) ∧
      PreservesFiniteColimits (extension R φ j) := by
  have : (extension R φ j).Additive := (moduleJAdj R φ j).left_adjoint_additive
  obtain ⟨A⟩ := semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)
  refine ⟨inferInstance, ?_⟩
  exact exact_of_componentwise (A := Modules R φ U) (B := Modules R φ X)
    (C := fun n ↦ StrictTower.Modules (R n) U)
    (D := fun n ↦ StrictTower.Modules (R n) X)
    (extension R φ j) (eval R φ X) (eval R φ U)
    (fun n ↦ StrictTower.moduleJ (R n) j) A.systems.componentwise
    (fun n ↦ (extensionEvaluation_exists R φ j n).some)

/-- Additivity of extension by zero.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
instance extensionAdditive {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension R φ j).Additive := (extension_exact R φ j).1

/-- Left exactness of extension by zero.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
instance extensionLimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (extension R φ j) := (extension_exact R φ j).2.1

/-- Right exactness of extension by zero.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
instance extensionColimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (extension R φ j) := (extension_exact R φ j).2.2

/-- Exact extension on the ordinary derived category of systems.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
abbrev J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (extension R φ j).mapDerivedCategory

/-- The derived open adjunction retains the ordinary units and counits.
Source: Stacks 03DI, 07A6 (blueprint: def-sp-varying-ring-operations). -/
def jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : J R φ j ⊣ G R φ j :=
  Adjunction.ofNatIsoRight (F := (pull R φ j).rightDerivedFunctor) (G := G R φ j)
    (H := J R φ j)
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (L := extension R φ j) (R := pull R φ j) (moduleJAdj R φ j))
    (pull R φ j).rightDerivedFunctorIsoMapDerivedCategory

/-- Ordinary open composition has the inverse-image composition as its conjugate.
Source: Stacks 03DI, 0F7D (blueprint: def-sp-varying-ring-operations). -/
def moduleJComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    extension R φ i ⋙ extension R φ j ≅ extension R φ (i ≫ j) :=
  Adjunction.leftAdjointCompIso
    (F₀₁ := extension R φ i) (F₁₂ := extension R φ j) (F₀₂ := extension R φ (i ≫ j))
    (G₁₀ := pull R φ i) (G₂₁ := pull R φ j) (G₂₀ := pull R φ (i ≫ j))
    (moduleJAdj R φ i) (moduleJAdj R φ j)
    (moduleJAdj R φ (i ≫ j)) (moduleGComp R φ i j).symm

/-- Derived open composition is localized from that ordinary comparison.
Source: Stacks 0F7D (blueprint: def-sp-varying-ring-operations). -/
def jComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] : J R φ i ⋙ J R φ j ≅ J R φ (i ≫ j) :=
  Functor.mapDerivedCategoryCompIso (extension R φ i) (extension R φ j) ≪≫
    Functor.mapDerivedCategoryNatIso (moduleJComp R φ i j)

/-- Identity extension with its canonical adjoint normalization.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def jId (X : Scheme.{u}) : J R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Adjunction.leftAdjointIdIso (F := J R φ (𝟙 X)) (G := G R φ (𝟙 X))
    (jAdj R φ (𝟙 X)) (gId R φ X)

/-- Evaluation on the ordinary unbounded derived category.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev ev (X : Scheme.{u}) (n : ℕ) := (eval R φ X n).mapDerivedCategory

/-- Derived evaluation is localization of the actual ordinary comparison.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def evalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    G R φ f ⋙ ev R φ X n ≅
      ev R φ Y n ⋙ (StrictTower.modulePullback (R n) f).mapDerivedCategory :=
  letI : (StrictTower.modulePullback (R n) f).Additive :=
    StrictTower.modulePullback_additive (R n) f
  letI : PreservesFiniteLimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteLimits (R n) f
  letI : PreservesFiniteColimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteColimits (R n) f
  Functor.mapDerivedCategoryCompIso (pull R φ f) (eval R φ X n) ≪≫
    Functor.mapDerivedCategoryNatIso (moduleEvalG R φ f n) ≪≫
      (Functor.mapDerivedCategoryCompIso (eval R φ Y n)
        (StrictTower.modulePullback (R n) f)).symm

/-- The ordinary exact-level adjunction, derived with its original unit.
Source: Stacks 07A6 (blueprint: def-sp-varying-ring-operations). -/
def levelAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (L := Scheme.proEtaleRingModulePullback f (coefficients R Y n) (coefficients R X n)
      (StrictTower.constantRingIso (R n) f))
    (R := Scheme.proEtaleRingModuleDirectImage f (coefficients R Y n) (coefficients R X n)
      (StrictTower.constantRingIso (R n) f))
    (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n) (coefficients R X n)
      (StrictTower.constantRingIso (R n) f))

/-- Evaluation of total direct image is the canonical mate, before inversion.
Source: Zheng 4.1, Lemma 4.10 (blueprint: def-sp-varying-ring-operations). -/
def evalPMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    P R φ f ⋙ ev R φ Y n ⟶
      ev R φ X n ⋙ (StrictTower.moduleDirectImage (R n) f).rightDerivedFunctor :=
  mateEquiv (L₁ := G R φ f) (R₁ := P R φ f)
    (L₂ := (StrictTower.modulePullback (R n) f).mapDerivedCategory)
    (R₂ := (StrictTower.moduleDirectImage (R n) f).rightDerivedFunctor)
    (G := ev R φ Y n) (H := ev R φ X n)
    (adj R φ f) (levelAdj R f n) (evalG R φ f n).inv

private noncomputable local instance (priority := 20000) fixedAb (X : Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (AlgebraicGeometry.Scheme.ProEt.topology X)

section FiniteEvaluationLeftAdjoints
set_option synthInstance.maxSize 128
open CategoryTheory.Functor SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify J AddCommGrpCat.{u + 1}]
  (B : ℕ → Sheaf J CommRingCat.{u + 1}) (τ : ∀ n, B (n + 1) ⟶ B n)
private def strictEquivalence [EssentiallySmall.{u + 1} C] :
    Systems.{u + 1, u, u + 1} J B τ ≌
      StrictRingSystem (rings.{u + 1, u, u + 1} J B τ) :=
  (strictSystemSequenceEquivalence (rings.{u + 1, u, u + 1} J B τ)).symm
private def evalIso [EssentiallySmall.{u + 1} C] (n : ℕ) :
    (strictEquivalence J B τ).functor ⋙
      systemEvaluation (rings.{u + 1, u, u + 1} J B τ) n ≅
    SemilinearSections.evaluation.{u + 1, u, u + 1} J B τ n := by
  change SheafOfModules.pushforward.{u + 1}
      (systemSequenceVerticalRingMap (rings.{u + 1, u, u + 1} J B τ) n) ≅
    SheafOfModules.pushforward.{u + 1}
      (eqToHom (evaluation_ring.{u + 1, u, u + 1} J B τ n).symm)
  exact SheafOfModules.pushforwardCongr (by
    ext V x
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl)

attribute [local irreducible] strictEquivalence

private theorem ordinary_preserves_resolving
    [EssentiallySmall.{u + 1} C] (n : ℕ)
    {P Q : CochainComplex (systemLevel (rings.{u + 1, u, u + 1} J B τ) n) ℤ}
    (f : P ⟶ Q) (hP : systemLevelKFlat (rings.{u + 1, u, u + 1} J B τ) n P)
    (hQ : systemLevelKFlat (rings.{u + 1, u, u + 1} J B τ) n Q) (hf : QuasiIso f) :
    QuasiIso (((((systemLevelLeftExtensionTheory (J := J)).some.single
      (rings.{u + 1, u, u + 1} J B τ) n).ordinary ⋙
      (strictEquivalence J B τ).inverse).mapHomologicalComplex (.up ℤ)).map f) := by
  let d := (systemLevelLeftExtensionTheory (J := J)).some.single
    (rings.{u + 1, u, u + 1} J B τ) n
  have := hf
  have := d.computes P hP
  have := d.computes Q hQ
  have hn := d.comparison.naturality f
  dsimp only [Functor.comp_map] at hn
  have he : DerivedCategory.Q.map
      ((d.ordinary.mapHomologicalComplex (.up ℤ)).map f) =
      inv (d.comparison.app P) ≫ d.derived.map (DerivedCategory.Q.map f) ≫
        d.comparison.app Q := by
    rw [hn, IsIso.inv_hom_id_assoc]
  have hq : QuasiIso ((d.ordinary.mapHomologicalComplex (.up ℤ)).map f) := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, he]
    infer_instance
  let E := (strictEquivalence J B τ).inverse
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  change QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map
    ((d.ordinary.mapHomologicalComplex (.up ℤ)).map f))
  have := hq
  infer_instance

private def ordinaryLeft [EssentiallySmall.{u + 1} C] (n : ℕ) :=
  ((systemLevelLeftExtensionTheory (J := J)).some.single
    (rings.{u + 1, u, u + 1} J B τ) n).ordinary ⋙ (strictEquivalence J B τ).inverse

private def ordinaryLeftAdj [EssentiallySmall.{u + 1} C] (n : ℕ) :
    ordinaryLeft J B τ n ⊣ SemilinearSections.evaluation.{u + 1, u, u + 1} J B τ n :=
  Adjunction.ofNatIsoRight
    (((systemLevelLeftExtensionTheory (J := J)).some.single
      (rings.{u + 1, u, u + 1} J B τ) n).ordinaryAdj.comp
        (strictEquivalence J B τ).symm.toAdjunction) (evalIso J B τ n)

private def derived_left_exists [EssentiallySmall.{u + 1} C] (n : ℕ) :
    SystemDerivedLeftExtension (SemilinearSections.evaluation.{u + 1, u, u + 1} J B τ n)
      (systemLevelKFlat (rings.{u + 1, u, u + 1} J B τ) n) := by
  have : (ordinaryLeft J B τ n).Additive := (ordinaryLeftAdj J B τ n).left_adjoint_additive
  exact (Classical.choice <| nonempty_normalizedLeftExtension
    (SemilinearSections.evaluation.{u + 1, u, u + 1} J B τ n)
    (ordinaryLeft J B τ n) (ordinaryLeftAdj J B τ n)
    (systemLevelKFlat (rings.{u + 1, u, u + 1} J B τ) n)
    (systemLevel_kFlatResolution (rings.{u + 1, u, u + 1} J B τ) n)
    (fun f hP hQ hf ↦ ordinary_preserves_resolving J B τ n f hP hQ hf)).toExtension

attribute [local irreducible] ordinaryLeft ordinaryLeftAdj derived_left_exists

private theorem changeR_map_transport
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (AlgebraicGeometry.Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (F G : AlgebraicGeometry.Scheme.proEtaleRingModules Y R ⥤
      AlgebraicGeometry.Scheme.proEtaleRingModules X
        ((AlgebraicGeometry.Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (h : F = G) {M N : AlgebraicGeometry.Scheme.proEtaleRingModules Y R} (a : M ⟶ N) :
    changeOfRingsHom.{u, u + 1, u + 1} c.hom (G.obj M) (G.map a) =
      eqToHom (congrArg (fun E : AlgebraicGeometry.Scheme.proEtaleRingModules Y R ⥤
        AlgebraicGeometry.Scheme.proEtaleRingModules X
          ((AlgebraicGeometry.Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ↦
        changeOfRings.{u, u + 1, u + 1} c.hom (E.obj M)) h.symm) ≫
      changeOfRingsHom.{u, u + 1, u + 1} c.hom (F.obj M) (F.map a) ≫
      eqToHom (congrArg (fun E : AlgebraicGeometry.Scheme.proEtaleRingModules Y R ⥤
        AlgebraicGeometry.Scheme.proEtaleRingModules X
          ((AlgebraicGeometry.Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ↦
        changeOfRings.{u, u + 1, u + 1} c.hom (E.obj N)) h) := by
  subst G
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem ringPull_preserves_flat
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (AlgebraicGeometry.Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P : CochainComplex (AlgebraicGeometry.Scheme.proEtaleRingModules Y R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((AlgebraicGeometry.Scheme.proEtaleRingModulePullback f R S c).mapHomologicalComplex
        (.up ℤ)).obj P) ∧
    ∀ i : ℤ, IsFlatOnSite (R := S)
      ((((AlgebraicGeometry.Scheme.proEtaleRingModulePullback f R S c).mapHomologicalComplex
        (.up ℤ)).obj P).X i) := by
  obtain ⟨I, hI⟩ := AlgebraicGeometry.Scheme.proEtaleAlgebraicInverseImage_exists f R
  have : PreservesFiniteLimits
      (AlgebraicGeometry.Scheme.proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  exact SheafOfModules.isKFlat_ringedToposPullback
    (AlgebraicGeometry.Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
    (AlgebraicGeometry.Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
    (AlgebraicGeometry.Scheme.proEtaleSheafAdjunction f (Type (u + 1))) I c.hom
    (AlgebraicGeometry.Scheme.proEtaleRingModulePullback f R S c)
    (fun M ↦ congrArg (fun F : AlgebraicGeometry.Scheme.proEtaleRingModules Y R ⥤
      AlgebraicGeometry.Scheme.proEtaleRingModules X
        ((AlgebraicGeometry.Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ↦
          changeOfRings.{u, u + 1, u + 1} c.hom (F.obj M)) hI.symm)
    (fun {M N} a ↦ changeR_map_transport f R S c I.modules
      (AlgebraicGeometry.Scheme.proEtaleModuleInverseImage f R) hI a) P hP hflat

private theorem square_fac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (s : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (mapDerivedCategorySquareIso s).hom.app (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((s.hom.mapHomologicalComplex (.up ℤ)).app K) := by
  have h₁ := mapDerivedCategoryCompIso_fac H I K
  have h₂ := mapDerivedCategoryCompIso_fac F G K
  have h₃ := mapDerivedCategoryNatIso_fac s K
  have hi : DerivedCategory.Q.map
      ((mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).hom.app K) = 𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = _
    exact DerivedCategory.Q.map_id _
  have hf : DerivedCategory.Q.map
      ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) = 𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = _
    exact DerivedCategory.Q.map_id _
  rw [hi] at h₁
  have h₁' : (mapDerivedCategoryCompIso H I).inv.app (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      (H ⋙ I).mapDerivedCategoryFactors.hom.app K := by
    exact (congrArg (fun z ↦ (mapDerivedCategoryCompIso H I).inv.app
      (DerivedCategory.Q.obj K) ≫ I.mapDerivedCategory.map
        (H.mapDerivedCategoryFactors.hom.app K) ≫ z)
        (Category.comp_id (I.mapDerivedCategoryFactors.hom.app
          ((H.mapHomologicalComplex (.up ℤ)).obj K)))).symm.trans h₁
  rw [hf] at h₂
  have h₂' : (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
    exact (congrArg (fun z ↦ (mapDerivedCategoryCompIso F G).inv.app
      (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K) ≫ z)
        (Category.comp_id (G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K)))).symm.trans h₂
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [h₁', h₃, ← h₂']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem square_symm
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (s : F ⋙ G ≅ H ⋙ I) :
    (mapDerivedCategorySquareIso s.symm).hom = (mapDerivedCategorySquareIso s).inv := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, mapDerivedCategoryNatIso_symm, Category.assoc]
private theorem inverseMateEqOfUnit
    {A B C D : Type u} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {P : B ⥤ A} {F' : C ⥤ D} {P' : D ⥤ C}
    (a : F ⊣ P) (b : F' ⊣ P') (E : A ⥤ C) (E' : B ⥤ D)
    (d : P ⋙ E ⟶ E' ⋙ P') (q : F ⋙ E' ≅ E ⋙ F')
    (hq : ∀ N, E.map (a.unit.app N) ≫ d.app (F.obj N) ≫
      P'.map (q.hom.app N) = b.unit.app (E.obj N)) :
    ((mateEquiv a b).symm d) = q.inv := by
  apply NatTrans.ext
  funext N
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu : E.map (a.unit.app N) ≫ d.app (F.obj N) =
      b.unit.app (E.obj N) ≫ P'.map (((mateEquiv a b).symm d).app N) :=
    unit_mateEquiv_symm a b d N
  rw [← hu]
  apply (cancel_mono (P'.map (q.hom.app N))).mp
  simp only [Category.assoc]
  rw [← P'.map_comp, Iso.inv_hom_id_app]
  exact (hq N).trans ((congrArg (fun z ↦ b.unit.app (E.obj N) ≫ z)
    (P'.map_id _)).trans (Category.comp_id _)).symm

open AlgebraicGeometry.ProEtale.VaryingRing AlgebraicGeometry.ProEtale
private theorem ordinary_finiteMate_iso
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {L : StrictTower.Modules (R n) Y ⥤ Modules R φ Y}
    {L' : StrictTower.Modules (R n) X ⥤ Modules R φ X}
    (a : L ⊣ eval R φ Y n) (b : L' ⊣ eval R φ X n) :
    IsIso ((mateEquiv a b).symm (moduleEvalG R φ f n).inv) := by
  let c := AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction f
    (coefficients R Y n) (coefficients R X n) (StrictTower.constantRingIso (R n) f)
  have h := inverseMateEqOfUnit (moduleAdj R φ f) c (eval R φ Y n)
    (eval R φ X n) (moduleEvalP R φ f n).hom (moduleEvalG R φ f n)
    (moduleEvalG_existsUnique R φ f n).choose_spec.1
  have hs : (mateEquiv (moduleAdj R φ f) c).symm (moduleEvalP R φ f n).hom =
      TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact congr_app h M
  have : IsIso (mateEquiv (moduleAdj R φ f) c
      (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv)) := by
    rw [← hs, Equiv.apply_symm_apply]
    infer_instance
  exact inverseMate_isIso_of_iterated a b c (moduleAdj R φ f) _

private theorem mate_isIso_of_inverseMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : F₁ ⊣ U₁) (d : F₂ ⊣ U₂)
    (τ : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂)
    (hi : IsIso ((mateEquiv a b).symm τ)) :
    IsIso (mateEquiv d c τ) := by
  have := hi
  have h := iterated_mateEquiv_conjugateEquiv a b c d ((mateEquiv a b).symm τ)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derived_finiteMate_iso
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (evalPMate R φ f n) := by
  let dY := derived_left_exists (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (coefficients R Y) (coefficientTransition R φ Y) n
  let dX := derived_left_exists (AlgebraicGeometry.Scheme.ProEt.topology X)
    (coefficients R X) (coefficientTransition R φ X) n
  have : (StrictTower.modulePullback (R n) f).Additive :=
    StrictTower.modulePullback_additive (R n) f
  have : PreservesFiniteLimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteLimits (R n) f
  have : PreservesFiniteColimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteColimits (R n) f
  let τ := (moduleEvalG R φ f n).inv
  have : IsIso ((mateEquiv dY.ordinaryAdj dX.ordinaryAdj).symm τ) :=
    ordinary_finiteMate_iso R φ f n dY.ordinaryAdj dX.ordinaryAdj
  let ι := asIso ((mateEquiv dY.ordinaryAdj dX.ordinaryAdj).symm τ)
  have hι (P) : dX.ordinaryAdj.homEquiv _ _ (ι.hom.app P) =
      (StrictTower.modulePullback (R n) f).map (dY.ordinaryAdj.unit.app P) ≫
      τ.app (dY.ordinary.obj P) := by
    rw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm dY.ordinaryAdj dX.ordinaryAdj τ P).symm
  have hτ (K : CochainComplex (Modules R φ Y) ℤ) :
      (evalG R φ f n).inv.app (DerivedCategory.Q.obj K) ≫
        (ev R φ X n).map ((pull R φ f).mapDerivedCategoryFactors.hom.app K) ≫
        (eval R φ X n).mapDerivedCategoryFactors.hom.app
          (((pull R φ f).mapHomologicalComplex (.up ℤ)).obj K) =
      (StrictTower.modulePullback (R n) f).mapDerivedCategory.map
        ((eval R φ Y n).mapDerivedCategoryFactors.hom.app K) ≫
        (StrictTower.modulePullback (R n) f).mapDerivedCategoryFactors.hom.app
          (((eval R φ Y n).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K) := by
    have he : (evalG R φ f n).inv =
        (Functor.mapDerivedCategorySquareIso (moduleEvalG R φ f n).symm).hom :=
      (square_symm (moduleEvalG R φ f n)).symm
    rw [he]
    exact square_fac (eval R φ Y n) (StrictTower.modulePullback (R n) f)
      (pull R φ f) (eval R φ X n) (moduleEvalG R φ f n).symm K
  have := derivedExtensionMate_isIso dY dX (StrictTower.modulePullback (R n) f)
    (pull R φ f) (StrictTower.modulePullback (R n) f).mapDerivedCategory
    (StrictTower.modulePullback (R n) f).mapDerivedCategoryFactors (evalG R φ f n).inv
    τ hτ ι hι
    (systemLevel_kFlatResolution
      (rings.{u + 1, u, u + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (coefficients R Y) (coefficientTransition R φ Y)) n)
    (fun P hP ↦ ringPull_preserves_flat f (coefficients R Y n) (coefficients R X n)
      (StrictTower.constantRingIso (R n) f) P hP.1 hP.2)
  have hD : IsIso ((mateEquiv dY.adjunction dX.adjunction).symm
      (evalG R φ f n).inv) := by
    change IsIso (derivedExtensionMate dY dX (pull R φ f)
      (StrictTower.modulePullback (R n) f).mapDerivedCategory (evalG R φ f n).inv)
    infer_instance
  exact mate_isIso_of_inverseMate dY.adjunction dX.adjunction
    (levelAdj R f n) (adj R φ f) (evalG R φ f n).inv hD
end FiniteEvaluationLeftAdjoints

/-- The canonical direct-image evaluation mate is invertible on all systems.
Source: Zheng 4.10; semilinear derived sections (blueprint: def-sp-varying-ring-operations).
Proof: transport the existing strict singleton left extension to actual sequence-site
modules. Its normalized derived adjunction is computed on flat-term K-flat complexes.
Pullback preserves this resolving class by the ringed-topos K-flat pullback theorem.
The ordinary unit normalization and iterated mates make the finite-extension mate
invertible. Its derived representative is invertible on resolving complexes, hence
everywhere. A second iterated-mates identity gives the prescribed evalPMate. -/
theorem evalPMate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (evalPMate R φ f n) := by
  exact derived_finiteMate_iso R φ f n

attribute [local irreducible] evalPMate

/-- The normalized derived direct-image evaluation.
Source: Zheng 4.10 (blueprint: def-sp-varying-ring-operations). -/
def evalP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  @asIso _ _ _ _ (evalPMate R φ f n) (evalPMate_isIso R φ f n)

/-- The exact-level open-extension adjunction.
Source: Stacks 03DI, 07A6 (blueprint: def-sp-varying-ring-operations). -/
def levelJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  Adjunction.ofNatIsoRight
    (F := (StrictTower.modulePullback (R n) j).rightDerivedFunctor)
    (G := (StrictTower.modulePullback (R n) j).mapDerivedCategory)
    (H := (StrictTower.moduleJ (R n) j).mapDerivedCategory)
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (L := StrictTower.moduleJ (R n) j) (R := StrictTower.modulePullback (R n) j)
      (StrictTower.moduleJAdj (R n) j))
      (StrictTower.modulePullback (R n) j).rightDerivedFunctorIsoMapDerivedCategory

/-- The open-extension evaluation comparison is fixed by the pullback comparison.
Source: Stacks 03DI; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def evalJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    ev R φ U n ⋙ (StrictTower.moduleJ (R n) j).mapDerivedCategory ⟶
      J R φ j ⋙ ev R φ X n :=
  (mateEquiv (L₁ := J R φ j) (R₁ := G R φ j)
    (L₂ := (StrictTower.moduleJ (R n) j).mapDerivedCategory)
    (R₂ := (StrictTower.modulePullback (R n) j).mapDerivedCategory)
    (G := ev R φ U n) (H := ev R φ X n)
    (jAdj R φ j) (levelJAdj R j n)).symm (evalG R φ j n).hom

section ExactMateLocalization
set_option synthInstance.maxSize 128
open CategoryTheory.Functor

section ExactAdjunction
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
private def exactAdj (a : L ⊣ R) : L.mapDerivedCategory ⊣ R.mapDerivedCategory := by
  let WA := HomotopyCategory.quasiIso A (.up ℤ)
  let WB := HomotopyCategory.quasiIso B (.up ℤ)
  have := Functor.isLeftDerivedFunctor_of_inverts WA L.mapDerivedCategory
    L.mapDerivedCategoryFactorsh
  have := Functor.isRightDerivedFunctor_of_inverts WB R.mapDerivedCategory
    R.mapDerivedCategoryFactorsh
  have := Functor.isLeftDerivedFunctor_of_inverts WA
    (L.mapDerivedCategory ⋙ R.mapDerivedCategory)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight L.mapDerivedCategoryFactorsh R.mapDerivedCategory)
  have : (R.mapDerivedCategory ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight R.mapDerivedCategoryFactorsh.inv L.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) WB := by
    convert Functor.isRightDerivedFunctor_of_inverts WB
      (R.mapDerivedCategory ⋙ L.mapDerivedCategory)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight R.mapDerivedCategoryFactorsh L.mapDerivedCategory) using 1
    ext X
    rfl
  exact (a.mapHomotopyCategory (.up ℤ)).derived WA WB
    L.mapDerivedCategoryFactorsh.hom R.mapDerivedCategoryFactorsh.inv
private theorem exactAdj_unit (a : L ⊣ R) (K : HomotopyCategory A (.up ℤ)) :
    (exactAdj a).unit.app (DerivedCategory.Qh.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.mapDerivedCategoryFactorsh.inv K
  change (exactAdj a).unit.app _ ≫ _ = _ at h
  rw [reassoc_of% h, Iso.inv_hom_id_app]
  exact Category.comp_id _
end ExactAdjunction

attribute [local irreducible] exactAdj

section ExactDerivedMates
open CategoryTheory.Functor
variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)

include adj₁ adj₂ in
private lemma exactDerivedMate_Qh
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (X : HomotopyCategory C₁ (.up ℤ)) :
    (exactAdj adj₂).unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
        g₂.mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) =
      u.mapDerivedCategory.map
          ((exactAdj adj₁).unit.app (DerivedCategory.Qh.obj X)) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app
          (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) := by
  -- reduce to a computation in the homotopy category
  rw [← cancel_epi (u.mapDerivedCategoryFactorsh.inv.app X),
    ← cancel_mono (g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)))]
  -- the left hand side
  have h₁ := (exactAdj adj₂).unit.naturality
    (u.mapDerivedCategoryFactorsh.inv.app X)
  have h₂ := exactAdj_unit adj₂
    ((u.mapHomotopyCategory (.up ℤ)).obj X)
  have h₃ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj β X
  have h₄ := g₂.mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
      (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h₁ h₄
  have h₂' : (exactAdj adj₂).unit.app
      (DerivedCategory.Qh.obj ((u.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X)) ≫
        g₂.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← h₂]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₃' := congrArg g₂.mapDerivedCategory.map h₃
  simp only [Functor.map_comp] at h₃'
  have hL : u.mapDerivedCategoryFactorsh.inv.app X ≫
      (exactAdj adj₂).unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X) ≫ (g₂.mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
            (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)) := by
    rw [reassoc_of% h₁, h₂']
    simp only [Category.assoc]
    rw [reassoc_of% h₃']
    simp only [Functor.map_comp, Category.assoc] at h₄ ⊢
    rw [h₄, Iso.inv_hom_id_app_assoc]
  -- the right hand side
  have k₁ := exactAdj_unit adj₁ X
  have k₁' : (exactAdj adj₁).unit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        g₁.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← k₁]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have k₂ := u.mapDerivedCategoryFactorsh.inv.naturality
    ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X)
  have k₃ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.inv.app X)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  have k₄ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj τ
    ((f₁.mapHomotopyCategory (.up ℤ)).obj X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at k₂
  have hR : u.mapDerivedCategoryFactorsh.inv.app X ≫
      u.mapDerivedCategory.map
        ((exactAdj adj₁).unit.app (DerivedCategory.Qh.obj X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((u.mapHomotopyCategory (.up ℤ)).map
        ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
          (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app _ ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _) := by
    rw [k₁']
    simp only [Functor.map_comp, Category.assoc]
    have hc : g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.hom.app X)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [← reassoc_of% k₂, reassoc_of% k₃, reassoc_of% hc]
    simp only [Functor.map_comp] at k₄ ⊢
    rw [k₄]
  simp only [Category.assoc]
  rw [hL, hR]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hu₂ : (adj₂.mapHomotopyCategory (.up ℤ)).unit.app ((u.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient C₁ (.up ℤ)).obj K)) =
      (HomotopyCategory.quotient C₂ (.up ℤ)).map ((adj₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((u.mapHomologicalComplex (.up ℤ)).obj K)) :=
    Adjunction.mapHomotopyCategory_unit_app_quotient _ adj₂ _
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient, hu₂]
  have hc : (adj₂.mapHomologicalComplex (.up ℤ)).unit.app
      ((u.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (g₂.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app K) =
      (u.mapHomologicalComplex (.up ℤ)).map ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
        (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app _ ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _ := by
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
    exact hβ (K.X n)
  have := (HomotopyCategory.quotient C₂ (.up ℤ)).congr_map hc
  simp only [Functor.map_comp] at this ⊢
  exact this

include adj₁ adj₂ in
/-- **The functors induced on derived categories preserve mates**: if `β : u ⋙ f₂ ≅ f₁ ⋙ v` is
the mate of `τ : g₁ ⋙ u ≅ v ⋙ g₂` for the adjunctions `f₁ ⊣ g₁` and `f₂ ⊣ g₂` of exact
functors, then the isomorphism induced by `β` on derived categories is the mate of the one
induced by `τ`, for the levelwise derived adjunctions `D(f₁) ⊣ D(g₁)` and `D(f₂) ⊣ D(g₂)`. -/
private lemma exactDerivedMate
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (K : DerivedCategory C₁) :
    (exactAdj adj₂).unit.app (u.mapDerivedCategory.obj K) ≫
        g₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      u.mapDerivedCategory.map ((exactAdj adj₁).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) := by
  have := Localization.essSurj (DerivedCategory.Qh (C := C₁)) (HomotopyCategory.quasiIso C₁ (.up ℤ))
  let e := DerivedCategory.Qh.objObjPreimageIso K
  rw [← cancel_epi (u.mapDerivedCategory.map e.hom)]
  have h₁ : u.mapDerivedCategory.map e.hom ≫
      (exactAdj adj₂).unit.app (u.mapDerivedCategory.obj K) =
      (exactAdj adj₂).unit.app (u.mapDerivedCategory.obj _) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom)) :=
    (exactAdj adj₂).unit.naturality _
  have h₂ : f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom) ≫
      (Functor.mapDerivedCategorySquareIso β).hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app _ ≫
        v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    (Functor.mapDerivedCategorySquareIso β).hom.naturality _
  have h₃ : e.hom ≫ (exactAdj adj₁).unit.app K =
      (exactAdj adj₁).unit.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    (exactAdj adj₁).unit.naturality _
  have h₄ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategory.map e.hom)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, ← Functor.map_comp_assoc, h₃,
    Functor.map_comp, Category.assoc, h₄,
    reassoc_of% (exactDerivedMate_Qh adj₁ adj₂ τ β hβ _)]

end ExactDerivedMates

private theorem localizedInverseMate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : A ⥤ B} {P : B ⥤ A} {L' : C ⥤ D} {P' : D ⥤ C}
    [L.Additive] [P.Additive] [L'.Additive] [P'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    (a : L ⊣ P) (b : L' ⊣ P') (E : A ⥤ C) (E' : B ⥤ D)
    [E.Additive] [E'.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
    (d : P ⋙ E ≅ E' ⋙ P')
    [IsIso ((mateEquiv a b).symm d.hom)] :
    IsIso ((mateEquiv (exactAdj a) (exactAdj b)).symm
      (Functor.mapDerivedCategorySquareIso d).hom) := by
  let β := asIso ((mateEquiv a b).symm d.hom)
  have hb (M : A) : b.unit.app (E.obj M) ≫ P'.map (β.hom.app M) =
      E.map (a.unit.app M) ≫ d.hom.app (L.obj M) :=
    (unit_mateEquiv_symm a b d.hom M).symm
  have hd := exactDerivedMate a b d β hb
  have he : ((mateEquiv (exactAdj a)
      (exactAdj b)).symm
      (Functor.mapDerivedCategorySquareIso d).hom) =
      (Functor.mapDerivedCategorySquareIso β).hom := by
    ext M
    apply ((exactAdj b).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have hu := unit_mateEquiv_symm (exactAdj a) (exactAdj b)
      (Functor.mapDerivedCategorySquareIso d).hom M
    change E.mapDerivedCategory.map ((exactAdj a).unit.app M) ≫
        (Functor.mapDerivedCategorySquareIso d).hom.app (L.mapDerivedCategory.obj M) =
      (exactAdj b).unit.app (E.mapDerivedCategory.obj M) ≫ P'.mapDerivedCategory.map
        (((mateEquiv (exactAdj a) (exactAdj b)).symm
          (Functor.mapDerivedCategorySquareIso d).hom).app M) at hu
    exact hu.symm.trans (hd M).symm
  rw [he]
  infer_instance

end ExactMateLocalization

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 128 in
private theorem derivedOpenMateIso
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    IsIso (evalJInv R φ j n) := by
  have : (StrictTower.moduleJ (R n) j).Additive :=
    (StrictTower.moduleJAdj (R n) j).left_adjoint_additive
  have : PreservesFiniteLimits (StrictTower.moduleJ (R n) j) :=
    (StrictTower.moduleJ_exact (R n) j).2.1
  have : PreservesFiniteColimits (StrictTower.moduleJ (R n) j) :=
    (StrictTower.moduleJ_exact (R n) j).2.2
  have : IsIso ((mateEquiv (moduleJAdj R φ j)
    (StrictTower.moduleJAdj (R n) j)).symm (moduleEvalG R φ j n).hom) :=
      ordinaryOpenMateIso R φ j n
  have := localizedInverseMate_isIso (moduleJAdj R φ j)
    (StrictTower.moduleJAdj (R n) j) (eval R φ U n) (eval R φ X n)
      (moduleEvalG R φ j n)
  have : IsIso ((mateEquiv (exactAdj (moduleJAdj R φ j))
      (exactAdj (StrictTower.moduleJAdj (R n) j))).symm
      (evalG R φ j n).hom) := by
    change IsIso ((mateEquiv (exactAdj (moduleJAdj R φ j))
      (exactAdj (StrictTower.moduleJAdj (R n) j))).symm
      (Functor.mapDerivedCategorySquareIso (moduleEvalG R φ j n)).hom)
    infer_instance
  exact inverseMateIsoOfOtherAdj (jAdj R φ j)
    (exactAdj (moduleJAdj R φ j))
    (levelJAdj R j n) (exactAdj (StrictTower.moduleJAdj (R n) j))
    (ev R φ U n) (ev R φ X n) (evalG R φ j n)

/-- The open-extension mate is the localization of the coefficientwise lift map.
Source: Stacks 03DI, 03DJ (blueprint: def-sp-varying-ring-operations).
Proof: the continuous open-site pullback has a unit given by restriction along the
site-adjunction counit. The identity section comparisons satisfy the evaluation unit
square. Uniqueness identifies its transported comparison with moduleEvalG. Taking
mates under evaluation/right-coextension and then under the open adjunctions gives
an invertible ordinary mate. Exact localization preserves its normalized unit square;
adjunction transport identifies the derived mate with the prescribed evalJInv. -/
theorem evalJInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    IsIso (evalJInv R φ j n) := by
  exact derivedOpenMateIso R φ j n

attribute [local irreducible] evalJInv

/-- Derived open evaluation with its specified unit normalization.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def evalJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  (@asIso _ _ _ _ (evalJInv R φ j n) (evalJInv_isIso R φ j n)).symm

attribute [instance] SemilinearSections.evaluationContinuous

end AlgebraicGeometry.ProEtale.VaryingRing
