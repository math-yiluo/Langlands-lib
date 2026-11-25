/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TensorOrdinaryCoordinates
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-ordinary-push-coordinates).

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

/-- The recorded fixed-module direct image, with a short name for coordinate equations.
Source: Levels (blueprint: def-sp-p1-ordinary-push-coordinates). -/
abbrev fixedPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f

/-- The recorded fixed-module adjunction, with its original unit and counit.
Source: Levels (blueprint: def-sp-p1-ordinary-push-coordinates). -/
abbrev fixedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f)

/-- Scalar-section-normalized ordinary direct-image coordinates.
Source: Levels (blueprint: def-sp-p1-ordinary-push-coordinates). -/
structure OrdinaryPushCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y) where
  ordinary : realization l E n X ⋙
      proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f ≅
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f ⋙
      realization l E n Y
  sections : ∀ (M : FixedSheaves l E n X) (U : Y.ProEtᵒᵖ)
    (m : M.obj.obj ((proEtaleBaseChange f).op.obj U)),
    (ordinary.hom.app M).val.app U
      (sfIntrinsicRealizationUnit X (SpTowerShriek.R l E n) M
        ((proEtaleBaseChange f).op.obj U) m) =
    sfIntrinsicRealizationUnit Y (SpTowerShriek.R l E n)
      ((ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f).obj M) U m

/-- The exact ordinary coordinate comparison applied termwise, before localization.
Source: Levels (blueprint: def-sp-p1-ordinary-push-coordinates). -/
def OrdinaryPushCoordinates.chain {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : OrdinaryPushCoordinates l E n f) (J : CochainComplex (FixedSheaves l E n X) ℤ) :=
  letI : (realization l E n X).Additive := realizationAdditive l E n X
  letI : (realization l E n Y).Additive := realizationAdditive l E n Y
  letI : (realization l E n X ⋙
    proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).PreservesZeroMorphisms :=
      inferInstance
  letI : (ProEtale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f ⋙
      realization l E n Y).PreservesZeroMorphisms := inferInstance
  (NatTrans.mapHomologicalComplex
    (F := realization l E n X ⋙
      proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f)
    (G := ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f ⋙
        realization l E n Y) c.ordinary.hom (.up ℤ)).app J

/-- The canonical K-injective source model for the actual constant-ring direct image.
Source: Levels (blueprint: def-sp-p1-ordinary-push-coordinates). -/
def realizedPushModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex (FixedSheaves l E n X) ℤ) [J.IsKInjective] :=
  letI : (realization l E n X).Additive := realizationAdditive l E n X
  letI : (realization l E n X).IsEquivalence := realizationEquivalence l E n X
  letI : CochainComplex.IsKInjective
    (((realization l E n X).mapHomologicalComplex (.up ℤ)).obj J) := inferInstance
  (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).rightDerivedFunctor.mapIso
    ((realization l E n X).mapDerivedCategoryFactors.app J) ≪≫
    (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).rightDerivedFunctorObjQIso
      (((realization l E n X).mapHomologicalComplex (.up ℤ)).obj J)

end AlgebraicGeometry.ProEtale.SpTowerP1
