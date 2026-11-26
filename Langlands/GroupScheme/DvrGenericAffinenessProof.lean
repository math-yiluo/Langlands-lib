import Langlands.GroupScheme.DvrGenericAffinenessReduction
import Langlands.GroupScheme.SmoothDvrGenericAffinenessProof
import Langlands.GroupScheme.DvrFiniteSmoothCoverProof

/-! # Proof of Raynaud's affineness criterion for group schemes over a DVR

The conditional reduction `DvrGenericAffinenessReduction.dvrGenericAffineness_of_smooth_and_cover`
applied to the proofs of its two premises, the smooth case `smoothDvrGenericAffineness` and the
finite smooth cover after a DVR extension `dvrFiniteSmoothCover`.
-/

universe u

namespace Langlands.GroupScheme

/-- A flat finite-type group scheme over a discrete valuation ring with affine generic fibre is
affine if and only if it is separated (Prasad--Yu, Proposition 3.1), in every universe. -/
theorem dvrGenericAffineness : DvrGenericAffinenessStatement.{u} :=
  DvrGenericAffinenessReduction.dvrGenericAffineness_of_smooth_and_cover
    smoothDvrGenericAffineness dvrFiniteSmoothCover

end Langlands.GroupScheme
