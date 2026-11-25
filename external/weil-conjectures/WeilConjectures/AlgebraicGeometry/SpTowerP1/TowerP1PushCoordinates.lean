/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1OrdinaryPushCoordinates
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-derived-push-coordinates).

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]

/-- The direct-image coordinates determined on every K-injective representative.
Source: Levels (blueprint: def-sp-p1-derived-push-coordinates). -/
structure PushCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y)
    extends OrdinaryPushCoordinates l E n f where
  derived : (realization l E n X).mapDerivedCategory ⋙
      (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).rightDerivedFunctor ≅
    (fixedPush l E n f).rightDerivedFunctor ⋙
        (realization l E n Y).mapDerivedCategory
  representative : ∀ (J : CochainComplex (FixedSheaves l E n X) ℤ) [J.IsKInjective],
    derived.hom.app (DerivedCategory.Q.obj J) ≫
      (realization l E n Y).mapDerivedCategory.map
        ((fixedPush l E n f).rightDerivedFunctorObjQIso J).hom ≫
      (realization l E n Y).mapDerivedCategoryFactors.hom.app
        (((fixedPush l E n f).mapHomologicalComplex (.up ℤ)).obj J) =
    (realizedPushModel l E n f J).hom ≫
      DerivedCategory.Q.map (toOrdinaryPushCoordinates.chain l E n J)

end AlgebraicGeometry.ProEtale.SpTowerP1
