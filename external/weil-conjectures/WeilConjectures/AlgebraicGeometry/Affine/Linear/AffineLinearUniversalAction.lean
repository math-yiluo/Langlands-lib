/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
/-! # Universal invertible matrices for the affine trace action

Source: linear-trace invariance, proof paragraph 1.
(blueprint: def-amb-affine-linear-universal-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry

attribute [local irreducible] Etale.rightDerivedLowerShriek
  Etale.affineLinearCompactComparison Etale.affineLinearCoefficientDescent

/-- The universal invertible matrix on the existing relative determinant-open. -/
def linearUniversalMatrix (S : Scheme.{u}) (d : ℕ) :
    Matrix.GeneralLinearGroup (Fin d) Γ((generalLinearOpen d S).toScheme, ⊤) :=
  Matrix.GeneralLinearGroup.mk''
    ((generalLinearOpen d S).ι.appTop.hom.mapMatrix (matrixCoord d S)) (by
      rw [← RingHom.map_det]
      exact (AffineSpace (ULift.{u} (Fin d × Fin d)) S).isUnit_ι_appTop_basicOpen
        (matrixCoord d S).det)

/-- Pulling the universal matrix back along a matrix section recovers that matrix.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: def-amb-affine-linear-universal-action). -/
theorem linearUniversalMatrix_specialize (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    Matrix.GeneralLinearGroup.map
        (generalLinearOpen.lift (𝟙 S) g.val (Matrix.isUnits_det_units g)).appTop.hom
        (linearUniversalMatrix S d) = g := by
  apply Units.ext
  ext i j
  change (generalLinearOpen.lift (𝟙 S) g.val (Matrix.isUnits_det_units g)).appTop
    ((generalLinearOpen d S).ι.appTop (matrixCoord d S i j)) = g i j
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, generalLinearOpen.lift_ι]
  simp only [matrixCoord, AffineSpace.homOfVector_appTop_coord]

/-- The determinant-open is finite type over its Noetherian base. -/
instance linearUniversal_noetherian (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    IsNoetherian (generalLinearOpen d S).toScheme := by
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin d × Fin d)) S) :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace (ULift.{u} (Fin d × Fin d)) S ↘ S)
  exact isNoetherian_of_locallyOfFiniteType (generalLinearOpen d S).ι

namespace Etale

/-- Invertibility of N pulls back to the universal parameter scheme. -/
theorem linearUniversalInvertible (N : ℕ) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    IsUnit (N : Γ((generalLinearOpen d S).toScheme, ⊤)) := by
  simpa only [map_natCast] using hS.map (generalLinearOpen.toBase d S).appTop.hom

/-- The actual affine trace source, independent of normalization data. -/
def linearActionObject (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (d : ℕ) : DerivedCategoryModule A S :=
  (affineTraceLeft A S d).obj ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))

/-- The existing specified linear action with its proved Cartesian square. -/
def linearActionMatrix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    linearActionObject A N hA S d ⟶ linearActionObject A N hA S d :=
  affineLinearTraceAction N hN A hA t S hS d (affineTraceLinearMap S d g)
    (affineTraceLinearMap_isPullback S d g)

end Etale
end AlgebraicGeometry
