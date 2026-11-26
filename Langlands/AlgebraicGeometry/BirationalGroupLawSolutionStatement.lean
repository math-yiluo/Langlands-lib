import Langlands.AlgebraicGeometry.BirationalGroupLaw
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Solutions of birational group laws over a discrete valuation ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every birational group law on a smooth, separated, faithfully flat scheme of finite type
over a discrete valuation ring has a solution. If the law is defined on the whole generic
fibre of `X ×_R X` and both universal translations map onto it there, so that the generic
fibre is a group under the law, the solution can be chosen with domain all of `X`. -/
def BirationalGroupLawSolutionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    Smooth f → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Surjective f →
    ∀ m : BirationalGroupLaw f,
      Nonempty m.Solution ∧
      ((∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R →
          p ∈ m.domain ∧
          p ∈ Set.range (leftTranslation f m.domain m.mul m.mul_comp).base ∧
          p ∈ Set.range (rightTranslation f m.domain m.mul m.mul_comp).base) →
        ∃ σ : m.Solution, σ.domain = ⊤)

end Langlands.AlgebraicGeometry
