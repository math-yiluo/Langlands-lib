import Langlands.ClassField.Global.CyclicInfinitePlaceLatticeHerbrandQuotientStatement
import Langlands.Cohomology.HerbrandPermutation

/-! # The cyclic Herbrand formula for the infinite-place integer lattice -/

open NumberField Langlands.Cohomology.Herbrand

namespace Langlands.ClassField.Global

universe u v

/-- The infinite-place integer permutation lattice has the Herbrand quotient
given by the product of its orbit stabilizer orders. -/
theorem cyclicInfinitePlaceLatticeHerbrandQuotient :
    CyclicInfinitePlaceLatticeHerbrandQuotient.{u, v} := by
  intro F _ _ E _ _ _ _ _
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact (hasHerbrandQuotient_natCast_iff _ _).1
    (hasHerbrandQuotient_ofMulAction (G := E ≃ₐ[F] E) (X := InfinitePlace E))

end Langlands.ClassField.Global
