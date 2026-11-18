import Langlands.GroupScheme.Reductive.RankOneCentralCoverStatement
import Langlands.GroupScheme.Reductive.CentralCoverRootOpposition
import Langlands.GroupScheme.Reductive.RankOneRootReducednessBaseChange

/-! # Rank-one reducedness from the actual central-cover statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The conditional implication from actual rank-one central covers to
rank-one reducedness over arbitrary fields. -/
def RankOneRootReducednessFromCentralCoverStatement : Prop :=
  RankOneCentralCoverStatement.{u} → RankOneRootReducednessStatement.{u}

/-- The actual rank-one central-cover statement implies rank-one reducedness over
algebraically closed fields, including the case of an empty root set. -/
theorem rankOneAlgClosedRootReducedness_of_centralCover
    (hcover : RankOneCentralCoverStatement.{u}) :
    RankOneAlgClosedRootReducednessStatement.{u} := by
  intro k _ _ G hG T hT i hi
  have := hG.isAffineHom
  have := hG.smooth
  intro hdep α hα β hβ
  obtain ⟨C, hC, f, t, hf, ht, hsq⟩ :=
    hcover k G hG T hT i hi ⟨α, hα⟩ hdep
  exact eq_or_eq_neg_of_sl2_centralCover hT i C hC f hf t ht hsq hα hβ

/-- The actual algebraically closed rank-one central-cover statement implies
rank-one reducedness over every field by actual-root base change. -/
theorem rankOneRootReducedness_of_centralCover
    : RankOneRootReducednessFromCentralCoverStatement.{u} :=
  fun hcover => rankOneRootReducedness_of_algClosed
    (rankOneAlgClosedRootReducedness_of_centralCover hcover)

end Langlands.GroupScheme
