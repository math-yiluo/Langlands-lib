/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompactificationScalarData
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompactificationOpenLimit
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompactificationPushLimit

/-!
# Complete compactification images: canonical limit realization
Source: blueprint paragraph (2)
(blueprint: lem-sp-complete-compactification-limit-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical strict-system scalar comparisons. The ordinary comparisons are
normalized before localization by the actual finite scalar maps. The derived direct-image
comparison is fixed by the two composition units on every cochain complex.
Source: blueprint paragraph (2), scalar comparisons and transition compatibility
(blueprint: lem-sp-complete-compactification-limit-realization). -/
structure ScalarComparison (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (h : ScalarSquares l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E c.Z)
    (DY : SpCoefficientTowersAbelian l E Y)
    (rX : SpReductionTower l E X DX) (rZ : SpReductionTower l E c.Z DZ)
    (rY : SpReductionTower l E Y DY)
    (aX : LimitPresentation l E X DX rX) (aZ : LimitPresentation l E c.Z DZ rZ)
    (aY : LimitPresentation l E Y DY rY)
    (vX : Evaluation l E b X DX) (vZ : Evaluation l E b c.Z DZ)
    (vY : Evaluation l E b Y DY) where
  openOrdinary : forgetting l E X DX ⋙ fixedOpenOrd l E c.i ≅
    ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z DZ
  open_normalized : ∀ (N : spCoefficientTowers l E X) (n : ℕ),
    (openOrdinary.hom.app N).app (op n) ≫
        (spCompletedEllRestriction l E c.Z n).map
          ((ordinaryOpenEvaluation l E b o c.i DX DZ vX vZ n).hom.app N) =
      (ordinaryOpenScalar l E b h c.i n).hom.app
        ((spCoefficientEvaluation l E X DX.equivalence n).obj N)
  pushOrdinary : forgetting l E c.Z DZ ⋙ fixedPushOrd l E c.g ≅
    ordinaryTowerPush l E b o c.g ⋙ forgetting l E Y DY
  push_normalized : ∀ (N : spCoefficientTowers l E c.Z) (n : ℕ),
    (pushOrdinary.hom.app N).app (op n) ≫
        (spCompletedEllRestriction l E Y n).map
          ((ordinaryPushEvaluation l E b o c.g DZ DY vZ vY n).hom.app N) =
      (ordinaryPushScalar l E h c.g n).hom.app
        ((spCoefficientEvaluation l E c.Z DZ.equivalence n).obj N)
  pushDerived : forgetDerived l E c.Z DZ rZ aZ ⋙
      (fixedPushOrd l E c.g).rightDerivedFunctor ≅
    towerPush l E b o c.g DZ DY ⋙ forgetDerived l E Y DY rY aY
  derived_normalized : IsPushScalarNormalized l E b o c.g DZ DY rZ rY aZ aY
    pushOrdinary pushDerived

/-- The normalization of direct-image evaluation on actual K-injective strict towers.
Source: blueprint paragraph (2); Stacks 0A07
(blueprint: lem-sp-complete-compactification-limit-realization). -/
def IsFixedPushEvaluation {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (v : (fixedPushOrd l E p).rightDerivedFunctor ⋙
        coefficientConstantTowerEvaluation l E Y n ≅
      coefficientConstantTowerEvaluation l E Z n ⋙ (pushOrd l E p).rightDerivedFunctor) :
    Prop :=
  ∀ (I : CochainComplex (Fixed l E Z) ℤ) [I.IsKInjective],
    (fixedEvaluation l E Y n).mapDerivedCategory.map
        ((fixedPushOrd l E p).rightDerivedFunctorObjQIso I).hom ≫
      (fixedEvaluation l E Y n).mapDerivedCategoryFactors.hom.app
        (((fixedPushOrd l E p).mapHomologicalComplex (.up ℤ)).obj I) =
    v.hom.app (DerivedCategory.Q.obj I) ≫
      (pushOrd l E p).rightDerivedFunctor.map
        ((fixedEvaluation l E Z n).mapDerivedCategoryFactors.hom.app I) ≫
      ((pushOrd l E p).rightDerivedFunctorObjQIso
        (((fixedEvaluation l E Z n).mapHomologicalComplex (.up ℤ)).obj I)).hom

/-- The actual augmentation to positive quotient n+1, before changing finite coordinates.
Its composite with the exact forgetting/evaluation isomorphism is the scalar adjunction
unit by LimitPresentation.unit_projection.
Source: blueprint paragraph (2), actual quotient augmentation
(blueprint: lem-sp-complete-compactification-limit-realization). -/
def quotientAugmentation (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : LimitPresentation l E T D r)
    (M : Integral l E T) (n : ℕ) :=
  (completionUnit l E T D r a).app M ≫
    (coefficientConstantTowerProjection l E T n).app
      ((forgetDerived l E T D r a).obj ((reduction l E T D r).obj M))

/-- The finite projection of the canonical strict scalar composite, before the
canonical finite-coordinate identification. The first two factors are the inverse
exact-open and derived-pushforward evaluation comparisons; the last is evaluation
of the strict scalar comparison itself, hence retains all semilinear transitions.
Source: blueprint paragraph (2), b_(n,N)
(blueprint: lem-sp-complete-compactification-limit-realization). -/
def finiteScalarComposite (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E c.Z)
    (DY : SpCoefficientTowersAbelian l E Y)
    (rX : SpReductionTower l E X DX) (rZ : SpReductionTower l E c.Z DZ)
    (rY : SpReductionTower l E Y DY)
    (aX : LimitPresentation l E X DX rX) (aZ : LimitPresentation l E c.Z DZ rZ)
    (aY : LimitPresentation l E Y DY rY)
    (e₀ : forgetting l E X DX ⋙ fixedOpenOrd l E c.i ≅
      ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z DZ)
    (d : forgetDerived l E c.Z DZ rZ aZ ⋙ (fixedPushOrd l E c.g).rightDerivedFunctor ≅
      towerPush l E b o c.g DZ DY ⋙ forgetDerived l E Y DY rY aY)
    (n : ℕ)
    (v : (fixedPushOrd l E c.g).rightDerivedFunctor ⋙
        coefficientConstantTowerEvaluation l E Y n ≅
      coefficientConstantTowerEvaluation l E c.Z n ⋙ (pushOrd l E c.g).rightDerivedFunctor)
    (N : spDerivedCoefficientTowers l E X DX) :=
  (pushOrd l E c.g).rightDerivedFunctor.map
      ((fixedOpenEvaluation l E c.i n).inv.app ((forgetDerived l E X DX rX aX).obj N)) ≫
    v.inv.app (((fixedOpenOrd l E c.i).mapDerivedCategory).obj
      ((forgetDerived l E X DX rX aX).obj N)) ≫
    (coefficientConstantTowerEvaluation l E Y n).map
      ((scalarComposite l E b o c DX DZ DY rX rZ rY aX aZ aY e₀ d).hom.app N)

attribute [local irreducible] scalarComposite pushLimit openLimit comparison
  finiteScalarComposite quotientAugmentation

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
