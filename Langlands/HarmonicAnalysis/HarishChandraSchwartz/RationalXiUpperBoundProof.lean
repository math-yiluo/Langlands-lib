import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundReduction

/-! # Waldspurger's upper bound for the actual Xi -/

universe u

namespace Langlands.HarishChandraSchwartz

/-- Waldspurger's upper bound in the weak split-component chamber, with one
degree for all pairs of translates. -/
theorem rationalXiUpperBound : RationalXiUpperBoundStatement.{u} :=
  rationalXiUpperBound_of_jacquetUnipotent.{u} rationalMinimalInducedJacquetUnipotent.{u}

end Langlands.HarishChandraSchwartz
