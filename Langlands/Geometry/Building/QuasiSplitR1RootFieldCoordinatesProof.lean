import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesReduction
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Type R1 coordinates for quasi-split groups -/

universe u

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

/-- Type R1 relative-root groups of quasi-split groups have root field coordinates. -/
theorem quasiSplitR1RootFieldCoordinates : QuasiSplitR1RootFieldCoordinatesStatement.{u} :=
  quasiSplitR1RootFieldCoordinates_of_structuralStatements
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy
    rootDatumExistence relativeRootSystem

end Langlands.Geometry.Building
