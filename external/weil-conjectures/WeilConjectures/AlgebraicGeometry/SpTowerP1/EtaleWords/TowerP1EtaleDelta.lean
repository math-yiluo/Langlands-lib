/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleOperations
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-! # Ordinary etale words for the projective-line tower comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Construction and Levels
(blueprint: def-sp-p1-etale-diagonal-word).

These are formulas in the ordinary etale derived categories. The diagonal is the
positive supported Cartier Kummer boundary; the trace is the second projection
of the inverse unit/Chern splitting. No adjunction unit is selected instead.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerP1.EtaleWords

variable (A : Type (u + 1)) [CommRing A]

variable [Finite A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)

/-- The ordinary shifted finite Tate line, at the actual annihilating exponent.
Source: Levels, twists and shifts (blueprint: def-sp-p1-etale-diagonal-word). -/
abbrev line (T : Scheme.{u}) := (Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧

/-- The positive supported Cartier class in total-derived direct-image coordinates.
Source: Construction, delta (blueprint: def-sp-p1-etale-diagonal-word). -/
def delta (S : Scheme.{u}) (hD : (diagonalImmersion S).ker.IsInvertible)
    (hW : IsUnit (N : Γ(diagonalSurface S, ⊤))) :
    (push A (diagonalImmersion S)).obj (Etale.ordinaryFiniteUnit A (ProjectiveLine S)) ⟶
      line A N hA (diagonalSurface S) :=
  Etale.supportedExactDerivedMap (Etale.lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion S))
    (Etale.ordinaryFiniteConstant A (ProjectiveLine S))
    (Scheme.finiteEtaleTateLine (diagonalSurface S) N A hA)
    (cartierReducedEtale A N hN hA (diagonalImmersion S) hD hW)

end AlgebraicGeometry.ProEtale.SpTowerP1.EtaleWords
