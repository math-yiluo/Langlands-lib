/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerKoszulIso

/-! # Data for the localized strict-tower zigzag

Source: Stacks Project, Tags 099N(5), 0G7E, 06XN, 03EL and 0FNH.
(blueprint: def-a1-finite-pullback-localized-zigzag-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FinitePullbackStrictTower
attribute [local implicit_reducible] HomologicalComplex.complexOfFunctorsToFunctorToComplex
attribute [local implicit_reducible] H tensorReduction augmentation G diagramPull
  finiteComplex pulledReduction transpose PrincipalQuotientCompletion.transpose
  koszulTowerComplex HomologicalComplex.asFunctor
  PrincipalKoszulStrictReplacement.sourceTower PrincipalKoszulStrictReplacement.targetTower
  FinitePullbackStrictTowerData.G FinitePullbackStrictTowerData.koszuls
  FinitePullbackStrictTowerData.reductions FinitePullbackStrictTowerData.diagramPull
  FinitePullbackStrictTowerData.finite FinitePullbackStrictTowerData.augmentation
  FinitePullbackStrictTowerData.H FinitePullbackStrictTowerData.tensorReduction
  FinitePullbackStrictTowerData.finiteComplex
  CompletedTowerIndependent.towerPull koszulTowerComplexMap
  PrincipalKoszulStrictReplacement.tensorWith
  PrincipalKoszulStrictReplacement.sourceTowerMap PrincipalKoszulStrictReplacement.targetTowerMap
attribute [local irreducible] CategoryTheory.Functor.map₂HomologicalComplex
  SheafOfModules.KFlatTotalTensorModel.tensor
attribute [local irreducible] CompletedTowerIndependent.reductionPair
  CompletedTowerIndependent.derivedPull CompletedTowerIndependent.derivedCounit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The given balanced isomorphism with the original strict-tower endpoints.
Source: Stacks 03EL and 06YY. The finite complex is expressed by its asFunctor diagram.
(blueprint: def-a1-finite-pullback-localized-zigzag-data). -/
def comparisonBalancedDiagramIso
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    (P : CochainComplex (Modules l E Y) ℤ) :
    tensorReduction l E X ((G l E g).obj P) ≅ ((finiteComplex l E g).obj P).asFunctor :=
  lambda.app P

end WeilConjectures.FinitePullbackStrictTower
