/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleEpsilon
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
(blueprint: def-sp-p1-etale-eta-word).

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

/-- The finite diagonal formula eta_n, using the actual supported class and mate inverses.
Source: Construction, eta (blueprint: def-sp-p1-etale-eta-word). -/
def eta (S : Scheme.{u}) (hD : (diagonalImmersion S).ker.IsInvertible)
    (hW : IsUnit (N : Γ(diagonalSurface S, ⊤)))
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (d : InvertibleWords A N hA S) (M : Etale.DerivedCategoryModule A (ProjectiveLine S)) :
    M ⟶ ((tensor A (ProjectiveLine S)).obj
      ((pull A (ProjectiveLine S ↘ S)).obj ((push A (ProjectiveLine S ↘ S)).obj M))).obj
        (line A N hA (ProjectiveLine S)) :=
  letI := d.diagonal M
  letI := d.exchange M
  letI := d.projection_two M
  sourceUnit A S true M ≫
    (push A (Etale.projectiveLineDiagonalProjection S true)).map
      (inv (diagonalProjection A S false M) ≫
        ((tensor A (diagonalSurface S)).map (delta A N hN hA S hD hW)).app _ ≫
        ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) (diagonalSurface S)).hom.app _).app _ ≫
        ((tensor A (diagonalSurface S)).obj _).map
          (Etale.ordinaryFiniteShiftedLinePullback A N hA t
            (Etale.projectiveLineDiagonalProjection S true)
            (finiteP1_unitOnPullback N (diagonalImmersion S) hW)).inv) ≫
    (@asIso _ _ _ _ (projection A (Etale.projectiveLineDiagonalProjection S true)
      ((pull A (Etale.projectiveLineDiagonalProjection S false)).obj M)
      (line A N hA (ProjectiveLine S))) (d.projection_two M)).inv ≫
    ((tensor A (ProjectiveLine S)).map (inv (exchange A S false M))).app _

end AlgebraicGeometry.ProEtale.SpTowerP1.EtaleWords
