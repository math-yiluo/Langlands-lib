import Langlands.Automorphic.GroupSchemeArithmeticHarishChandraInduction
import Langlands.Automorphic.GroupSchemeHarishChandraParabolicReduction
import Langlands.Automorphic.GroupSchemeLeviCenterRestrictionProof
import Langlands.Global.AdelicSquareIntegrableProjectionAutomorphyProof

/-! # Finite-dimensional span of projections of square-integrable automorphic forms -/

namespace Langlands.Global

open Langlands.Automorphic.GroupSchemeFunctions

/-- The projections of a square-integrable automorphic form onto closed invariant subspaces
of `L²([G])` lie in a single finite-dimensional subspace. -/
theorem squareIntegrableFormFiniteProjection : SquareIntegrableFormFiniteProjectionStatement := by
  have hCenter : ParabolicLeviCenterRestrictionStatement.{0} := parabolicLeviCenterRestriction
  exact squareIntegrableFormFiniteProjection_of_reduction
    (parabolicHarishChandraFiniteness_of_arithmetic_and_center
      (arithmeticHarishChandraFiniteness_of_leviCenterRestriction hCenter) hCenter)
    squareIntegrableProjectionAutomorphy

end Langlands.Global
