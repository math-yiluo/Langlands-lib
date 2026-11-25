/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralClassPullback

/-! # The intermediate integral-coefficient inverse image

Source: blueprint classes proof (2), coefficient realization through the intermediate
quotient tower (blueprint: def-sp-tower-chern-pullback-intermediate).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The intermediate inverse image on the actual Z/ell-power module systems.
The forgetful square is on whole abelian towers. Its unit is fixed by the integral
generator, and its root comparison is part of a morphism of the actual Kummer
sequences whose last component is pullback of full units. Thus a root comparison
cannot be chosen independently of that boundary.
Source: classes (2), realization steps 1--4
(blueprint: def-sp-tower-chern-pullback-intermediate). -/
structure IntegralCoefficientPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cY : Chern l E Y) (cX : Chern l E X) where
  pull : Systems Y (Rrings l Y) ⥤ Systems X (Rrings l X)
  [additive : pull.Additive]
  [limits : PreservesFiniteLimits pull]
  [colimits : PreservesFiniteColimits pull]
  forgetIso : cY.reduction.forget.F ⋙ abPull f ≅ pull ⋙ cX.reduction.forget.F
  unitIso : pull.obj (coefficient Y (Rrings l Y)) ≅ coefficient X (Rrings l X)
  rootIso : pull.obj cY.rootModule ≅ cX.rootModule
  unit_normalization :
    (abPull f).map (integerGenerator Y (Rrings l Y) cY.reduction.forget) ≫
        forgetIso.hom.app (coefficient Y (Rrings l Y)) ≫
        cX.reduction.forget.F.map unitIso.hom =
      integerPull f ≫ integerGenerator X (Rrings l X) cX.reduction.forget
  kummer :
    (abPull f).mapShortComplex.obj
        (ShortComplex.mk cY.kummer.inclusion cY.kummer.power cY.kummer.zero) ⟶
      ShortComplex.mk cX.kummer.inclusion cX.kummer.power cX.kummer.zero
  kummer_roots : kummer.τ₁ =
    (abPull f).map cY.rootForget.inv ≫ forgetIso.hom.app cY.rootModule ≫
      cX.reduction.forget.F.map rootIso.hom ≫ cX.rootForget.hom
  kummer_units : kummer.τ₃ = unitsPull f

attribute [instance] IntegralCoefficientPullback.additive
  IntegralCoefficientPullback.limits IntegralCoefficientPullback.colimits

variable {l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
  {cY : Chern l E Y} {cX : Chern l E X}

/-- Exact localization of the intermediate coefficient-unit map.
Source: classes (2), single-complex comparison
(blueprint: def-sp-tower-chern-pullback-intermediate). -/
def IntegralCoefficientPullback.derivedUnit
    (d : IntegralCoefficientPullback l E f cY cX) :
    d.pull.mapDerivedCategory.obj (unit Y (Rrings l Y)) ≅ unit X (Rrings l X) :=
  (d.pull.mapDerivedCategorySingleFunctor 0).app (coefficient Y (Rrings l Y)) ≪≫
    (DerivedCategory.singleFunctor (Systems X (Rrings l X)) 0).mapIso d.unitIso

/-- Exact localization of the root map, including the specified shift comparison.
Source: classes (2), positive-kernel root identification
(blueprint: def-sp-tower-chern-pullback-intermediate). -/
def IntegralCoefficientPullback.derivedRoot
    (d : IntegralCoefficientPullback l E f cY cX) (n : ℤ) :
    d.pull.mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (Systems Y (Rrings l Y)) 0).obj
          cY.rootModule)⟦n⟧) ≅
      ((DerivedCategory.singleFunctor (Systems X (Rrings l X)) 0).obj cX.rootModule)⟦n⟧ :=
  (d.pull.mapDerivedCategory.commShiftIso n).app _ ≪≫
    (shiftFunctor (D X (Rrings l X)) n).mapIso
      ((d.pull.mapDerivedCategorySingleFunctor 0).app cY.rootModule ≪≫
        (DerivedCategory.singleFunctor (Systems X (Rrings l X)) 0).mapIso d.rootIso)

/-- The scalar counit on the shifted root module, before integral reduction.
Source: classes (2), scalar extension of the positive root line
(blueprint: def-sp-tower-chern-pullback-intermediate). -/
def scalarRootTarget {T : Scheme.{u}} (c : Chern l E T) :
    c.scalar.T.obj
        (((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
          c.rootModule)⟦(2 : ℤ)⟧) ⟶ (line l E c)⟦(2 : ℤ)⟧ :=
  (c.scalar.T.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj c.rootModule) ≫
    (lineComparison l E c)⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.SpTowerClasses
