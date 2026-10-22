import Langlands.Representation.Hecke.TestFunction

/-! # Common compact-open bi-invariance of finitely many Hecke test functions -/

universe u

namespace Langlands.Hecke.TestFunction

/-- Every finite set of actual test functions is bi-invariant under a common
compact open subgroup contained in any prescribed open subgroup. -/
def CommonCompactOpenBiInvarianceStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    ∀ (s : Finset (Langlands.HarmonicAnalysis.SchwartzBruhat G)) (U : OpenSubgroup G),
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧
        ∀ f ∈ s, f ∈ biInvariant K.toSubgroup K.toSubgroup

end Langlands.Hecke.TestFunction
