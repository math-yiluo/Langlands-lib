/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted

/-! # Normalization predicates for finite Tate descent

Source: Stacks Project, Tags 03PK and 099R.
The definitions are retained verbatim from `FiniteTateSiteDescent`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The existing finite quotient ring, lifted only to the sheaf universe.
Source: coefficient notation (blueprint: def-pur-finite-tate-site-comparison). -/
abbrev finiteTateCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})

/-- Restrict the recorded finite Tate module to its constant scalar action.
Source: Stacks Tag 03CY (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateConstantRestriction :
    SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n) ⥤
      Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) :=
  letI := purTwistForgetPreservesSheafification T
  SheafOfModules.restrictScalars
      ((constantCommuteCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (finiteTateCoefficient l E n))).inv ⋙
    constantRingModuleRestriction (ProEt.topology T) (finiteTateCoefficient l E n)

/-- The original finite pro-etale twist, in the fixed-coefficient encoding.
Source: coefficient-twist blueprint, order 1505
(blueprint: def-pur-finite-tate-site-comparison). -/
abbrev finiteTateProSheaf (a : ℕ) :=
  (finiteTateConstantRestriction l E n T).obj (finiteCoefficientTwist l E T n (a : ℤ))

/-- A sectionwise pure tensor in the first finite twist.
Source: Stacks Tag 03EK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateProGenerator (W : T.ProEtᵒᵖ)
    (a : finiteTateCoefficient l E n)
    (x : (purTwistZlOne T l).obj.obj W) :
    (finiteTateProSheaf l E n T 1).obj.obj W :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E T n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient T l E n) (purTwistIntegralOne T l E))).app W)
    (((realizationRingUnit (ProEt.topology T)
      (finiteTateCoefficient l E n)).app W a) ⊗ₜ[_,
        ((purTwistIntegralQuotient T l E n).hom.app W).hom]
      (purTwistIntegralTensor T l E W 1 x))

/-- Pure local tensors in the prescribed nonnegative pro-etale powers.
Source: Stacks Tag 03EK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateProPowerGenerator (W : T.ProEtᵒᵖ)
    (a : finiteTateCoefficient l E n) :
    (k : ℕ) → (Fin k → (purTwistZlOne T l).obj.obj W) →
      (finiteTateProSheaf l E n T k).obj.obj W
  | 0, _ => (realizationRingUnit (ProEt.topology T)
      (finiteTateCoefficient l E n)).app W a
  | 1, x => finiteTateProGenerator l E n T W a (x 0)
  | k + 2, x => SheafOfModules.siteSheafTensorTmul
      (coefficientTwistPower T (purTwistFiniteOne T l E n) (k + 1))
      (purTwistFiniteOne T l E n) W
      (finiteTateProPowerGenerator W a (k + 1) (fun i ↦ x i.castSucc))
      (finiteTateProGenerator l E n T W 1 (x (Fin.last (k + 1))))

/-- Pure local tensors in the recorded etale Tate powers.
Source: Stacks Tags 03PK and 03EK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateEtalePowerGenerator (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (W : T.Etaleᵒᵖ) (a : A) :
    (k : ℕ) → (Fin k → (T.rootsOfUnitySheaf m).obj.obj W) →
      (finiteEtaleTateTwist T m A hA k).obj.obj W
  | 0, _ => (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a
  | 1, x => finiteEtaleTateOneGenerator A m T hA W a (x 0)
  | k + 2, x =>
      (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (finiteEtaleTateTwist T m A hA (k + 1)) (finiteEtaleTateLine T m A hA)).app W
        (finiteTateEtalePowerGenerator A m hA W a (k + 1) (fun i ↦ x i.castSucc) ⊗ₜ[A]
          finiteEtaleTateOneGenerator A m T hA W 1 (x (Fin.last (k + 1))))

/-- The actual unit underlying a finite root section on the etale site.
Source: Stacks Tag 03PK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateEtaleRootValue (m : ℕ) (W : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf m).obj.obj W) : Γ(W.unop.left, ⊤)ˣ :=
  Additive.toMul (((kernel.ι (m • 𝟙 T.gmSheaf)).hom.app W z).down)

/-- The actual unit in a specified projection of the root limit.
Source: Stacks Tag 03PK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateLimitRootValue (r : ℕ) (W : T.ProEtᵒᵖ)
    (x : (purTwistZlOne T l).obj.obj W) : Γ(W.unop.left, ⊤)ˣ :=
  Additive.toMul (((proEtaleRootsOfUnityInclusion T (l ^ (r + 1))).hom.app W
    ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app W x)).down)

/-- Root-projection normalization of the comparison, on every local pure tensor.
The arrow `f` allows arbitrary pro-etale tests over an etale object, so roots may be
lifted to the infinite root tower pro-etale locally, without requiring an etale lift.
Source: Stacks Tags 03PK and 0GLZ
(blueprint: def-pur-finite-tate-site-comparison). -/
def IsFiniteTateSiteComparison (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (b : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop)
    (a : finiteTateCoefficient l E n)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U)
    (x : Fin k → (purTwistZlOne T l).obj.obj W),
    (∀ i : Fin k, finiteTateLimitRootValue l T r W (x i) =
      Units.map f.left.appTop.hom.toMonoidHom (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i))) →
    b.hom.hom.app W
      (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k)).obj.map f.op
        (((ProEtale.comparisonAdjunction
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).unit.app
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k)).hom.app U
              (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z))) =
      finiteTateProPowerGenerator l E n T W a k x

/-- The pullback comparison on etale powers is fixed on root tensors.
Source: Stacks Tags 03PK and 03Q1
(blueprint: def-pur-finite-tate-site-comparison). -/
def IsFiniteTateEtalePullback {T' : Scheme.{u}} (v : T' ⟶ T) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (c : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
      (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
        finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U)
    (z' : Fin k → (T'.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj
      ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)),
    (∀ i : Fin k,
      finiteTateEtaleRootValue T' (l ^ (r + 1)) _ (z' i) =
        Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
          (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i))) →
    ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).homEquiv _ _ c.hom).hom.app U
        (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z) =
      finiteTateEtalePowerGenerator T' _ (l ^ (r + 1)) hA _ a k z'

/-- The usual pro-etale pullback comparison, fixed by every root projection.
Source: Stacks Tag 09A5; the root tower limit universal property
(blueprint: def-pur-finite-tate-site-comparison). -/
def IsFiniteTateProPullback {T' : Scheme.{u}} (v : T' ⟶ T) (k : ℕ)
    (b : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
      (finiteTateProSheaf l E n T k) ≅ finiteTateProSheaf l E n T' k) : Prop :=
  ∀ (U : T.ProEtᵒᵖ) (a : finiteTateCoefficient l E n)
    (x : Fin k → (purTwistZlOne T l).obj.obj U)
    (x' : Fin k → (purTwistZlOne T' l).obj.obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ v).op.obj U)),
    (∀ (s : ℕ) (i : Fin k), finiteTateLimitRootValue l T' s _ (x' i) =
      Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
        (finiteTateLimitRootValue l T s U (x i))) →
    ((ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).homEquiv _ _ b.hom).hom.app U
        (finiteTateProPowerGenerator l E n T U a k x) =
      finiteTateProPowerGenerator l E n T' _ a k x'

/-- The exponent-change comparison is induced by the specified root power map.
Source: Stacks Tag 03PK (blueprint: def-pur-finite-tate-site-comparison). -/
def IsFiniteTateEtaleTransition (r r' : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (t : finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
      finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
    (z' : Fin k → (T.rootsOfUnitySheaf (l ^ (r' + 1))).obj.obj U)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U),
    (∀ i : Fin k, finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i) =
      finiteTateEtaleRootValue T (l ^ (r' + 1)) U (z' i) ^ (l ^ (r' - r))) →
    t.hom.hom.app U (finiteTateEtalePowerGenerator T _ (l ^ (r' + 1)) hA' U a k z') =
      finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z

end AlgebraicGeometry.Scheme
