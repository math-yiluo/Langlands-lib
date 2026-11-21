import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexReductionToE6D4
import Langlands.GroupScheme.SimplyConnected.LocalRankOneE6Exclusion
import Langlands.GroupScheme.SimplyConnected.LocalRankOneD4Exclusion

/-! # Enumeration of actual rank-one Tits indices over local fields -/

universe u

namespace Langlands.GroupScheme

/-- The exact five alternatives for actual rank-one Tits indices over
nonarchimedean local fields, in every field and residue characteristic. -/
theorem localRankOneTitsIndex : LocalRankOneTitsIndexStatement.{u} := by
  intro K _ _ _ _ G _ _ d hsc has hrank
  rcases localRankOneTitsIndexReductionToE6D4 K G d hsc has hrank with h | hE6 | hD4
  · exact h
  · exact (d.not_hasRankOneE6BranchIndex hsc hE6).elim
  · exact (d.not_hasRankOneD4InnerOrNoFixedLeafIndex hsc hD4).elim

end Langlands.GroupScheme
