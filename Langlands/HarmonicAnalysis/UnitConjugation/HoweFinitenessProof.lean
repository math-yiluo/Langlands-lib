import Langlands.HarmonicAnalysis.UnitConjugation.HoweFinitenessReduction
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentOrderProof

/-!
# Howe's finiteness theorem on the Lie algebra of the unit group of a semisimple local algebra

This module proves `Langlands.HarmonicAnalysis.LieAlgebraHoweFinitenessStatement`
(`lieAlgebraHoweFiniteness`) by applying the reduction
`UnitConjugation.lieAlgebraHoweFinitenessReduction` to the existence of a compact open order
with idempotent generators of all left ideals, `UnitConjugation.semisimpleIdempotentOrder`.
-/

universe u v

namespace Langlands.HarmonicAnalysis

/-- **Howe's finiteness theorem** (Harish-Chandra's Theorem 12.1) for the Lie algebra of the unit
group of a finite-dimensional semisimple algebra over a nonarchimedean local field of
characteristic zero. -/
theorem lieAlgebraHoweFiniteness : LieAlgebraHoweFinitenessStatement.{u, v} :=
  UnitConjugation.lieAlgebraHoweFinitenessReduction UnitConjugation.semisimpleIdempotentOrder

end Langlands.HarmonicAnalysis
