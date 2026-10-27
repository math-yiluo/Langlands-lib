import Langlands.HarmonicAnalysis.Distribution.Subspace

/-!
# Unique descent of distributions supported on a closed subset

An internal generalization of the remark after Shalika (1974), Lemma 1.15,
from closed submanifolds to arbitrary closed subsets of Hausdorff, locally
compact, totally disconnected spaces, with pointwise-annihilator support.
-/

namespace Langlands.HarmonicAnalysis.Distribution

universe u

/-- For every Hausdorff, locally compact, totally disconnected space `X` and
every closed subset `Z ⊆ X`, with its induced subtype topology, the closed
pushforward `closedPushforwardSupported hZ : Distribution Z →ₗ[ℂ] supportedOn Z`
is bijective: every algebraic distribution on `X` that annihilates each test
function vanishing at every point of `Z` equals `D ∘ restrictClosed hZ` for
exactly one algebraic distribution `D` on `Z`. -/
def ClosedSupportedDescentStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (Z : Set X) (hZ : IsClosed Z),
      Function.Bijective (closedPushforwardSupported hZ)

end Langlands.HarmonicAnalysis.Distribution
