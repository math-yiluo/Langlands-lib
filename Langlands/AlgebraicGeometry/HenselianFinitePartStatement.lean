import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Henselian

/-! # The finite part over a Henselian local ring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- An open and closed subscheme finite over a local base and containing its
whole closed fibre. -/
structure IsFiniteClosedFibrePart (U : X.Opens) : Prop where
  isClosed : IsClosed (U : Set X)
  isFinite : IsFinite (U.ι ≫ f)
  contains_closedFibre : ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U

/-- The finite clopen part of a separated quasi-finite finite-type scheme over
a Henselian local ring, derived from EGA IV4, Theorem 18.5.11(c). -/
def HenselianFinitePartStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f → IsSeparated f →
      ∃ U : X.Opens, IsFiniteClosedFibrePart f U

end Langlands.AlgebraicGeometry
