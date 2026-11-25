/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1PushCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleWords
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-geometric-coordinates).

The coordinates retain the canonical associated-module-sheaf functor. Its tensor
comparison is fixed on scalar-unit pure tensors, on total-complex summands, and
on K-flat representatives. Thus the final level equations cannot be satisfied
by choosing unrelated isomorphisms of their endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]

/-- Pullback coordinates are the adjoint of the normalized direct-image coordinates.
This mate equality fixes the actual unit and counit, including scalar normalization.
Source: Levels (blueprint: def-sp-p1-geometric-coordinates). -/
structure GeometricCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y)
    extends PushCoordinates l E n f where
  pull : (realization l E n Y).mapDerivedCategory ⋙
      proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f ≅
    (ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f).mapDerivedCategory ⋙
        (realization l E n X).mapDerivedCategory
  mate : (mateEquiv
    (fixedAdjunction l E n f)
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f)) pull.hom) = derived.inv

/-- Exact site inverse-image coordinates, including the canonical left-derived/exact iso.
Source: Levels (blueprint: def-sp-p1-geometric-coordinates). -/
def exactSitePull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    EtaleWords.pull (ULift.{u + 1} (SpTowerShriek.R l E n)) f ⋙
        (comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) X).mapDerivedCategory ≅
    (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) Y).mapDerivedCategory ⋙
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f).mapDerivedCategory :=
  Functor.isoWhiskerRight
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f) _ ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The ordinary total-derived direct-image mate; its restriction is fixedComparison's mate.
Source: Levels (blueprint: def-sp-p1-geometric-coordinates). -/
def exactSitePush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f)
    (fixedAdjunction l E n f) (exactSitePull l E n f).inv)

end AlgebraicGeometry.ProEtale.SpTowerP1
