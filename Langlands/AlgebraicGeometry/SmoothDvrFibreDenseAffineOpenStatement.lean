import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # A fibre-dense affine open of a smooth scheme over a DVR -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A smooth quasi-compact separated scheme over a DVR has an affine open such that every
point has a generization in that open lying in the same fibre. -/
def SmoothDvrFibreDenseAffineOpenStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R)),
    Smooth p → QuasiCompact p → IsSeparated p →
    ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ x : X, ∃ y : X, y ∈ U ∧ p y = p x ∧ y ⤳ x

end Langlands.AlgebraicGeometry
