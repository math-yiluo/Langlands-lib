/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleDelta
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
(blueprint: def-sp-p1-etale-word-invertibility).

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

/-- Only invertibility of named finite arrows, used to spell their inverses.
These are conclusions in the tower comparison theorem, not hypotheses on its inputs.
Source: Construction (blueprint: def-sp-p1-etale-word-invertibility). -/
structure InvertibleWords (S : Scheme.{u}) : Prop where
  projection_q : ∀ K : Etale.DerivedCategoryModule A S,
    IsIso (projection A (ProjectiveLine S ↘ S) (line A N hA (ProjectiveLine S)) K)
  projection_two : ∀ M : Etale.DerivedCategoryModule A (ProjectiveLine S),
    IsIso (projection A (Etale.projectiveLineDiagonalProjection S true)
      ((pull A (Etale.projectiveLineDiagonalProjection S false)).obj M)
      (line A N hA (ProjectiveLine S)))
  diagonal : ∀ M : Etale.DerivedCategoryModule A (ProjectiveLine S),
    IsIso (diagonalProjection A S false M)
  exchange : ∀ M : Etale.DerivedCategoryModule A (ProjectiveLine S),
    IsIso (exchange A S false M)

end AlgebraicGeometry.ProEtale.SpTowerP1.EtaleWords
