import Langlands.AlgebraicGeometry.StrictBirationalGroupLaw
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian

/-! # Strict birational group laws over a strictly henselian discrete valuation ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Over a strictly henselian discrete valuation ring `R`, a birational group law on a smooth,
separated, faithfully flat scheme `X` of finite type which restricts to a strict law on an
`R`-dense open subscheme `X'` has a solution whose domain is `X'`: an open immersion of `X'`
with `R`-dense image into a smooth separated `R`-group scheme of finite type whose group law
restricts to the law on `X'`. -/
def StrictBirationalGroupLawHenselianSolutionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    Smooth f → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Surjective f →
    ∀ (m : BirationalGroupLaw f) (X' : X.Opens),
      FibreGenerizationDense f (X' : Set X) → m.IsStrictOn X' →
        ∃ σ : m.Solution, σ.domain = X'

end Langlands.AlgebraicGeometry
