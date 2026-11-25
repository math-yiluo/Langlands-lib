/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.FourierTransform.FdCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap

/-! # Common strict towers for the two completed pullbacks

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; Stacks 099N(2),(5) and 0941
(blueprint: lem-fd-pullback-common-strict-tower-models).

The helper definitions retain the actual reduction tower, derived counits and
coefficient identity. `FdCommonStrictTowerModels` packages its strict comparisons,
both cone coordinates and the resolution-normalized natural comparison.
`fdPullbackCommonStrictTowerModels` states existence under the node's hypotheses.
-/

@[expose] public noncomputable section
set_option genCtorIdx false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual PBC strict quotient tower on the fixed coefficient presentation.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonStrictTower {U T : Scheme.{u}} (h : U ⟶ T) :
    CochainComplex (integralTowerModules l E T) ℤ ⥤
      CochainComplex (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ :=
  (fdCoefficientTransport l E T).mapHomologicalComplex (.up ℤ) ⋙
    completedReductionComplexTowerFunctor T (pbcIntegralDatum l E) ⋙
      (completedTowerModulePullback h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)

/-- The fixed endomorphism of the framework strict quotient tower.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonFrameworkEnd {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (∏ᶜ (fun n ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n))) ⟶
      (∏ᶜ (fun n ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n))) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n))
    (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E h).obj P))

/-- The fixed unshifted quotient projection of the framework cone.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonFrameworkProjection {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ) (n : ℕ) :
    ((integralOperationsPullbackComplexFunctor l E h).obj P).X i ⟶
      (((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n)).X i :=
  (CochainComplex.mappingCocone.fst (fdCommonFrameworkEnd l E h P)).f i ≫
    (Pi.π (fun k ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op k)) n).f i

/-- The shifted quotient projection of the framework cone.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonFrameworkShiftedProjection {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (p : ℤ) (n : ℕ) :
    ((integralOperationsPullbackComplexFunctor l E h).obj P).X (p + 1) ⟶
      (((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n)).X p :=
  (CochainComplex.mappingCocone.snd (fdCommonFrameworkEnd l E h P)).v
    (p + 1) p (by omega) ≫
      (Pi.π (fun k ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op k)) n).f p

/-- The canonical unit generator in the actual strict quotient tower.
Source: Stacks 099N(5), trace-definition final sentence
(blueprint: lem-fd-pullback-common-strict-tower-models). -/
def fdCommonStrictGenerator {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ) (n : ℕ) (V : T.ProEt)
    (x : ((fdCoefficientTransport l E T).obj (P.X i)).val.obj (op V)) :
    (((fdCommonStrictTower l E h).obj P).X i).obj (op n) |>.val.obj
      (op ((proEtaleBaseChange h).obj V)) :=
  pbcActualModuleUnitSection h (pbcIntegralDatum l E)
    ((completedReductionLevel T (pbcIntegralDatum l E) n).obj
      ((fdCoefficientTransport l E T).obj (P.X i))) V
    (reductionTensorSection T (completedReductionProjection T (pbcIntegralDatum l E) n)
      ((fdCoefficientTransport l E T).obj (P.X i)) (op V) 1 x)

attribute [local irreducible] fdCommonStrictTower fdCommonFrameworkEnd fdCommonFrameworkProjection
  fdCommonFrameworkShiftedProjection fdCommonStrictGenerator integralDetailedTransport
  integralDerivedPullback integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor fdCoefficientTransport

end WeilConjectures
