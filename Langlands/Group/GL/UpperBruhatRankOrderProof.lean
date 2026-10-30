import Langlands.Group.GL.UpperBruhatRankOrderStatement
import Langlands.Group.GL.UpperBruhatBoundaryProof

/-! Proof of strict inversion growth for permutations ordered by their lower-left corner counts. -/

namespace Langlands.GeneralLinear

/-- Distinct permutations whose lower-left corner counts are dominated have strictly
fewer inversions. This is the published combinatorial comparison
`UpperBruhatBoundary.rankOrderInversion`, whose type is the statement verbatim. -/
theorem upperBruhatRankOrderInversion : UpperBruhatRankOrderInversionStatement :=
  UpperBruhatBoundary.rankOrderInversion

end Langlands.GeneralLinear
