/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
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

/-! # Augmented strict reduction tower of ordinary pullback

## Main definitions

* `IsStrictNormalized` fixes the strict finite tensor comparison before localization.
* `limitComparison` is the specified inverse-limit isomorphism induced by a tower comparison.

These definitions are shared by the strict-model descent and its derived-limit comparison.

## References

* Stacks Project, Tag 099N, proof of (5), paragraph 2
* Stacks 099L
* Stacks 099N(5)
* Stacks 03D7
* Stacks 03EL
* Stacks 03EK, 099N(5)
* Stacks 06YY, 099N(5)
* Stacks 0940, 099N(5)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.PulledReduction
attribute [local instance] completedModulePullback_additive
attribute [local instance] completedTowerModulePullback_additive
attribute [local instance] completedReductionModuleTowerFunctor_additive
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Constant scalar restriction, on the original small site. -/
abbrev res (T : Scheme.{t}) := proEtaleRingRestrictScalars (exchangeScalar d T)

/-- Exact inverse image of constant-coefficient modules. -/
abbrev pull := proEtaleRingModulePullback g (exchangeConstantRing Y A)
  (exchangeConstantRing X A) (exchangeConstantIso g A)

/-- Ordinary constant-coefficient pullback after restriction; its exact derived functor
is N in the statement. -/
abbrev ordinarySource := res d Y ⋙ pull (A := A) g

/-- N, on all ambient objects, without a completeness or boundedness hypothesis. -/
def source := (ordinarySource d g).mapDerivedCategory

/-- The pulled-back completed-coefficient strict reduction tower H. -/
def tower := completedReductionTower Y d ⋙ completedTowerPullback g d

/-- Ordinary restriction on strict towers, retaining all transitions. -/
abbrev tres (T : Scheme.{t}) := exchangeTowerModuleRes d T

/-- The ordinary strict pulled quotient diagram, before localization. -/
abbrev ordinaryReductionTarget := completedReductionModuleTowerFunctor Y d ⋙
  completedTowerModulePullback g d ⋙ tres d X

/-- Zero maps for the entire ordinary strict comparison. -/
local instance ordinaryReductionTarget_preservesZeroMorphisms :
    (ordinaryReductionTarget d g).PreservesZeroMorphisms where
  map_zero M N := by
    have h := Functor.map_zero (completedReductionModuleTowerFunctor Y d) M N
    have h' := Functor.map_zero (completedTowerModulePullback g d)
      ((completedReductionModuleTowerFunctor Y d).obj M)
      ((completedReductionModuleTowerFunctor Y d).obj N)
    have h'' := Functor.map_zero (tres d X)
      ((completedTowerModulePullback g d).obj ((completedReductionModuleTowerFunctor Y d).obj M))
      ((completedTowerModulePullback g d).obj ((completedReductionModuleTowerFunctor Y d).obj N))
    exact (congrArg (tres d X).map
      ((congrArg (completedTowerModulePullback g d).map h).trans h')).trans h''

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar-insertion section for completed module pullback. Apply the actual
model-site pullback adjunction unit at the transported object, then insert 1.
The up/down module transports preserve section carriers definitionally, so this
is the unit of the constructed inverse image, with no choice of an adjunction. -/
def insertion (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedModulePullback g d).obj M).val.obj ((proEtaleBaseChange g).op.obj U) := by
  letI : (proEtaleModelBaseChange g).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
    proEtaleModelBaseChange_isContinuous g
  exact reductionTensorSection X (completedCoefficientMap g d)
    ((proEtaleModuleInverseImage g (d.completedRing Y)).obj M)
    ((proEtaleBaseChange g).op.obj U) 1
    (((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
      (F := proEtaleModelBaseChange g)
      (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
      (proEtaleModelRingUnit g (d.completedRing Y))).unit.app
        ((proEtaleModuleToModel (reductionModuleRing Y (d.completedRing Y))).obj M)).val.app
          (AsSmall.up.op.obj U) x)

/-- Degreewise scalar insertion as a map of the actual pulled complexes.
The target is written as the successive two complex functors, retaining their
already fixed zero-map instances. -/
def ordinaryComplexComparison
    (s : ordinarySource d g ⟶ completedModulePullback g d ⋙ res d X)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    ((ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((res d X).mapHomologicalComplex (.up ℤ)).obj
        (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) where
  f i := s.app (P.X i)
  comm' i j _ := (s.naturality (P.d i j)).symm

/-- The comparison from H on a K-flat completed model to its ordinary pulled quotient
complex. Its invertibility is asserted only on the specified resolving class below. -/
def targetCounit (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    ((tower d g) ⋙ (tres d X).mapDerivedCategory).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryReductionTarget d g).mapHomologicalComplex (.up ℤ)).obj P) :=
  (tres d X).mapDerivedCategory.map
      ((completedTowerPullback g d).map (completedReductionTowerComplexCounit Y d P) ≫
        completedTowerPullbackComplexCounit g d
          ((completedReductionComplexTowerFunctor Y d).obj P)) ≫
    (tres d X).mapDerivedCategoryFactors.hom.app
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        ((completedReductionComplexTowerFunctor Y d).obj P))

/-- Exact evaluation commutes with restriction of the entire strict diagram. -/
def evaluationRes (T : Scheme.{t}) (n : ℕ) :
    (tres d T).mapDerivedCategory ⋙
        reductionTowerDerivedEvaluation T (reductionModuleRing T (exchangeConstantRing T A)) n ≅
      reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n ⋙
        (res d T).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso
    (Iso.refl (tres d T ⋙ reductionTowerEvaluation T
      (reductionModuleRing T (exchangeConstantRing T A)) n))

/-- Rho is Rlim(tau) inverse after the specified restriction/limit comparison. This
uses the normalized K-injective limit comparison already recorded in the library. -/
def limitComparison
    (τ : source d g ⋙ OrderedExchange.reduction d X ≅
      tower d g ⋙ (tres d X).mapDerivedCategory)
    (K : reductionDerivedCategory Y (d.completedRing Y)) :
    (res d X).mapDerivedCategory.obj
        ((completedRlim X (d.completedRing X)).obj ((tower d g).obj K)) ≅
      (OrderedExchange.completion d X).obj ((source d g).obj K) :=
  (OrderedExchange.lambda d X).app ((tower d g).obj K) ≪≫
    (OrderedExchange.rlim (A := A) X).mapIso (τ.app K).symm

end AlgebraicGeometry.Scheme.PulledReduction
