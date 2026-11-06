import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs

/-! # The root-generated centralizer bound from rank-one factorization -/

universe u

namespace Langlands.GroupScheme

/-- The exact rank-one factorization statement suffices for the exact
root-generated centralizer statement, with no other geometric premise. -/
def RootGeneratedCentralizerRankOneReductionStatement : Prop :=
  RootRankOneFactorizationStatement.{u} → RootGeneratedCentralizerRankOneStatement.{u}

/-- Opposite pairs give the root-system input by averaging, and the
assembled word and kernel argument gives the target. -/
theorem rootGeneratedCentralizerRankOneReduction :
    RootGeneratedCentralizerRankOneReductionStatement.{u} := by
  intro hRank
  exact rootGeneratedCentralizerRankOne_of_structuralPremises
    ⟨relativeRootSystemStatement_of_rootRankOneFactorizationStatement hRank, hRank⟩

end Langlands.GroupScheme
