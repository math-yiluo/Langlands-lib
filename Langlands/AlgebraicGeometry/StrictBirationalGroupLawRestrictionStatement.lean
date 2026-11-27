import Langlands.AlgebraicGeometry.StrictBirationalGroupLaw
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Birational group laws over a discrete valuation ring are strict on a dense open -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every birational group law on a smooth, separated, faithfully flat scheme of finite type
over a discrete valuation ring `R` restricts to a strict birational group law on some
`R`-dense open subscheme. -/
def StrictBirationalGroupLawRestrictionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    Smooth f → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Surjective f →
    ∀ m : BirationalGroupLaw f,
      ∃ X' : X.Opens, FibreGenerizationDense f (X' : Set X) ∧ m.IsStrictOn X'

end Langlands.AlgebraicGeometry
