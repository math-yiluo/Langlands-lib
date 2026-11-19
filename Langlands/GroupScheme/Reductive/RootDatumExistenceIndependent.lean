import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Reductive.RankOneCentralCoverProof
import Langlands.GroupScheme.Reductive.RankOneRootReducednessFromCentralCover
import Langlands.GroupScheme.Reductive.RootDatumFromRankOneReducedness

/-! # Existence of split reductive root data via rank-one central covers -/

universe u

namespace Langlands.GroupScheme

/-- A split maximal torus of a connected reductive group has a finite reduced root datum
on its character and cocharacter lattices, by rank-one central covers. -/
theorem rootDatumExistenceIndependent : RootDatumExistenceStatement.{u} :=
  rootDatumExistence_of_rankOneReducedness
    (rankOneRootReducedness_of_centralCover rankOneCentralCover)

end Langlands.GroupScheme
