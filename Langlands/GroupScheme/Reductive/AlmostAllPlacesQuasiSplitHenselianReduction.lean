import Langlands.GroupScheme.Reductive.AlmostAllPlacesQuasiSplitClauseReduction
import Langlands.GroupScheme.Reductive.AlmostAllPlacesTorsorPoints

/-! # Almost all places quasi-split, from henselian quasi-splitness

The published `HenselianFiniteResidueQuasiSplitStatement` implies the published
`AlmostAllPlacesQuasiSplitStatement`. The quasi-splitness clause is
`almostAllPlacesQuasiSplitClauseReduction`; the torsor clause is the unconditional
`AlmostAllPlacesTorsorPoints.eventually_nonempty_ringPoint_of_torsor`. -/

universe u

namespace Langlands.GroupScheme

/-- The implication from henselian quasi-splitness (Conrad, Exercise 5.5.3(ii), for
henselian local rings with finite residue field) to quasi-splitness and torsor points at
almost all finite places of a number field (Conrad, Exercise 5.5.3(iii)). -/
def AlmostAllPlacesQuasiSplitHenselianReductionStatement : Prop :=
  HenselianFiniteResidueQuasiSplitStatement.{u} → AlmostAllPlacesQuasiSplitStatement.{u}

/-- `AlmostAllPlacesQuasiSplitStatement` from `HenselianFiniteResidueQuasiSplitStatement`. -/
theorem almostAllPlacesQuasiSplit_of_henselian
    (hH : HenselianFiniteResidueQuasiSplitStatement.{u}) :
    AlmostAllPlacesQuasiSplitStatement.{u} :=
  fun F _ _ G hG =>
    ⟨almostAllPlacesQuasiSplitClauseReduction hH F G hG,
      fun X _ hfl hs hqc hiso =>
        AlmostAllPlacesTorsorPoints.eventually_nonempty_ringPoint_of_torsor F G hG X hfl hs hqc hiso⟩

/-- Proof of `AlmostAllPlacesQuasiSplitHenselianReductionStatement`. -/
theorem almostAllPlacesQuasiSplitHenselianReduction :
    AlmostAllPlacesQuasiSplitHenselianReductionStatement.{u} :=
  almostAllPlacesQuasiSplit_of_henselian

end Langlands.GroupScheme
