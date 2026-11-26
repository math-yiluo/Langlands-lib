import Langlands.AlgebraicGeometry.BirationalGroupLaw
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Birational group laws that are group laws on the generic fibre -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Let `m` be a birational group law on a smooth, separated, faithfully flat scheme `X` of
finite type over a discrete valuation ring `R`. If `m` is defined on the whole generic fibre of
`X ×_R X` and both universal translations map onto it there, and `m` has a solution, then `m`
has a solution whose domain is all of `X`. -/
def BirationalGroupLawGenericGroupSolutionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    Smooth f → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Surjective f →
    ∀ m : BirationalGroupLaw f,
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R →
          p ∈ m.domain ∧
          p ∈ Set.range (leftTranslation f m.domain m.mul m.mul_comp).base ∧
          p ∈ Set.range (rightTranslation f m.domain m.mul m.mul_comp).base) →
        Nonempty m.Solution → ∃ σ : m.Solution, σ.domain = ⊤

end Langlands.AlgebraicGeometry
