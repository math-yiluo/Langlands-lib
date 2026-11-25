/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
import all WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm

/-! # The specified ordered affine right normal form

This file defines the specified ordered normal form and its degree-zero Tate product,
exposing the construction used in the proof of the affine-space trace.

## Implementation details

`orderedAffineRightIso` is the recursive construction itself, not a choice from `Nonempty`.
-/

public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar
set_option backward.isDefEq.respectTransparency true

/-- The direct pullback, ordered Tate power, and accumulated even shift. -/
@[expose]
def orderedAffineRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A S ⥤ DerivedCategoryModule A (affineTraceTower S d)
  | 0 => 𝟭 _
  | d + 1 => ordinaryFinitePullback A (affineTraceProjection S (d + 1)) ⋙
      derivedTensorRight (ModuleCat.{u + 1} A) (affineTraceTower S (d + 1))
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N (affineTraceTower S (d + 1)) hA
            ((d + 1 : ℕ) : ℤ))) ⋙ shiftFunctor _ (2 * ((d + 1 : ℕ) : ℤ))

/-- The isomorphism between `affineTraceRight` and its ordered normal form `orderedAffineRight`. -/
@[irreducible]
def orderedAffineRightIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → affineTraceRight A N hA S d ≅ orderedAffineRight A N hA S d
  | 0 => Iso.refl _
  | d + 1 => AlgebraicGeometry.Etale.towerENormalForm (ModuleCat.{u + 1} A) N
      (fun X e ↦ Scheme.finiteEtaleTateSheaf A N X hA (e : ℤ))
      (fun f hY e ↦ (Scheme.finiteEtaleTwistPullbackData A N hN hA).c f hY
        (affineTracePullbackInvertible N f hY) e)
      (fun _ ↦ Iso.refl _) (fun X hX e ↦
        AlgebraicGeometry.Etale.twistFlat A N hN hA X hX e)
      (fun X hX e ↦ AlgebraicGeometry.Etale.twistSheafProduct A N hA
        (Scheme.finiteEtaleTwistPullbackData A N hN hA) X hX e) S hS (d + 1)

end AlgebraicGeometry.Etale
