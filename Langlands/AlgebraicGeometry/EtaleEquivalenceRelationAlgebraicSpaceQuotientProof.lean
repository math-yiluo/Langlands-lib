import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientReduction
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Proof

/-! # The algebraic-space quotient of an étale equivalence relation -/

universe u

namespace Langlands.AlgebraicGeometry

/-- Stacks Project Lemma 02WW, presentation form: every étale equivalence relation has an
algebraic-space quotient, namely the fppf sheaf quotient of its slice relation. -/
theorem etaleEquivalenceRelationAlgebraicSpaceQuotient :
    EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u} :=
  etaleEquivalenceRelationAlgebraicSpaceQuotient_of
    LocallyQuasiFiniteDescent.fppfSeparatedLocallyQuasiFiniteDescent

end Langlands.AlgebraicGeometry
