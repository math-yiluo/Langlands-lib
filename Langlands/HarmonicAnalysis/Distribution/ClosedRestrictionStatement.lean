import Langlands.HarmonicAnalysis.Distribution.Subspace

/-!
# Restriction of Schwartz–Bruhat functions to closed subsets is surjective

An internal generalization of Shalika (1974), Lemma 1.15, from closed
submanifolds to arbitrary closed subsets of Hausdorff, locally compact, totally
disconnected spaces.
-/

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

universe u

/-- For every Hausdorff, locally compact, totally disconnected space `X` and
every closed subset `Z ⊆ X`, with its induced subtype topology, the restriction
map `restrictClosed hZ : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Z` is surjective:
every locally constant, compactly supported complex function on `Z` is the
restriction of one on `X`. -/
def ClosedRestrictionSurjectiveStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (Z : Set X) (hZ : IsClosed Z),
      Function.Surjective (restrictClosed hZ)

end Langlands.HarmonicAnalysis.SchwartzBruhat
