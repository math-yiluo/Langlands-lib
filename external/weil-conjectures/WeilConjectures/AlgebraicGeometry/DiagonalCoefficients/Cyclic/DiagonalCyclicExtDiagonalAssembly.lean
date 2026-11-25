/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicExtEvaluationAssembly

/-! # Ext assembly at one evaluation of strict diagonal systems

Source: diagonal limit (3).
(blueprint: lem-diagonal-cyclic-ext-diagonal-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local instance 4000] cyclicCoefficientHasExt

attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.homEquiv
  Ext.comp Ext.mk₀ Ext.mapExactFunctor Functor.mapDerivedCategory shiftFunctor

/-- Specialize evaluation assembly to the diagonal coefficient categories, while
keeping every object, endpoint and class abstract.
Source: diagonal limit (3) (blueprint: lem-diagonal-cyclic-ext-diagonal-assembly).
Proof: apply the evaluation assembly with the supplied localization choices of
module sheaves and their systems. No geometric endpoint is substituted here. -/
theorem cyclicExtAssembly_diagonal
    (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    [DiagonalTraceLocalizations l W]
    [eSys : HasExt.{u + 1} (DiagonalSystems l W)] (k : ℕ) :
    cyclicEvaluationAssemblySpec
      (A := DiagonalMod l W)
      (C₀ := DerivedCategory.{u + 1} (DiagonalCompleted l W))
      (dA := DiagonalTraceLocalizations.mod (ℓ := l) (X := W))
      (dS := DiagonalTraceLocalizations.systems (ℓ := l) (X := W))
      (eA := cyclicCoefficientHasExt l W)
      (eS := eSys) k := by
  exact cyclicExtAssembly_atLevel
    (A := DiagonalMod l W)
    (C₀ := DerivedCategory.{u + 1} (DiagonalCompleted l W))
    (dA := DiagonalTraceLocalizations.mod (ℓ := l) (X := W))
    (dS := DiagonalTraceLocalizations.systems (ℓ := l) (X := W))
    (eA := cyclicCoefficientHasExt l W)
    (eS := eSys) k

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
