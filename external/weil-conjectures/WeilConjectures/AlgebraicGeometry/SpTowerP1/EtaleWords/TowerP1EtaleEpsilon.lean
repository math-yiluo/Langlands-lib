/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleFiniteData
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
(blueprint: def-sp-p1-etale-epsilon-word).

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

/-- The finite splitting-trace formula epsilon_n, with no abstract adjunction counit.
Source: Construction, epsilon (blueprint: def-sp-p1-etale-epsilon-word). -/
def epsilon (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (b : Etale.ArbitraryBaseFiniteP1Splitting A N hA t S hS)
    (d : InvertibleWords A N hA S) (K : Etale.DerivedCategoryModule A S) :
    (push A (ProjectiveLine S ↘ S)).obj
      (((tensor A (ProjectiveLine S)).obj
        ((pull A (ProjectiveLine S ↘ S)).obj K)).obj
          (line A N hA (ProjectiveLine S))) ⟶ K :=
  letI : IsIso (projection A (ProjectiveLine S ↘ S) (line A N hA (ProjectiveLine S)) K) :=
    d.projection_q K
  (push A (ProjectiveLine S ↘ S)).map
    (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) (ProjectiveLine S)).hom.app _).app _) ≫
    (@asIso _ _ _ _ (projection A (ProjectiveLine S ↘ S) (line A N hA (ProjectiveLine S)) K)
      (d.projection_q K)).inv ≫
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app _).app K ≫
    ((tensor A S).obj K).map b.trace ≫ (Etale.derivedTensorSingleUnitIso K).hom

end AlgebraicGeometry.ProEtale.SpTowerP1.EtaleWords
