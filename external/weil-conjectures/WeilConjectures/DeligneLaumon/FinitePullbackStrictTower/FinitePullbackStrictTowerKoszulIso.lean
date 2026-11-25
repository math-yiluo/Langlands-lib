/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerComparisonData

/-! # Localization of the pulled Koszul isomorphism

Source: Stacks Project, Tags 099N(5), 0G7E, 06XN, 03EL and 0FNH.
(blueprint: def-a1-finite-pullback-localized-koszul-iso).
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
attribute [local implicit_reducible] H tensorReduction augmentation G diagramPull
  finiteComplex pulledReduction transpose PrincipalQuotientCompletion.transpose
  koszulTowerComplex HomologicalComplex.asFunctor
  PrincipalKoszulStrictReplacement.sourceTower PrincipalKoszulStrictReplacement.targetTower
  FinitePullbackStrictTowerData.G FinitePullbackStrictTowerData.koszuls
  FinitePullbackStrictTowerData.reductions FinitePullbackStrictTowerData.diagramPull
  FinitePullbackStrictTowerData.finite FinitePullbackStrictTowerData.augmentation
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

/-- The given Koszul isomorphism with the original strict-tower endpoints.
Source: Stacks 0G7E. This is the same diagram isomorphism with explicit endpoints.
(blueprint: def-a1-finite-pullback-localized-koszul-iso). -/
def comparisonKoszulDiagramIso
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (P : CochainComplex (Modules l E Y) ℤ) :
    (diagramPull l E g).obj (H l E Y P) ≅ H l E X ((G l E g).obj P) :=
  θ.app P

end WeilConjectures.FinitePullbackStrictTower
