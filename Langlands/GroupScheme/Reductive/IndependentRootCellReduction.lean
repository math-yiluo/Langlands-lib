import Langlands.GroupScheme.Reductive.RankOneCentralCoverStatement
import Langlands.GroupScheme.Reductive.CentralCoverRootOpposition
import Langlands.GroupScheme.Reductive.RankOneCentralCoverLines
import Langlands.GroupScheme.Reductive.RankOneSupportLinesBaseChange
import Langlands.GroupScheme.Reductive.LocalRankOneRootCell

/-! # The rank-one root-cell theorem from an independent standard central cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A supplied independent geometric cover theorem gives the geometric support and lines. -/
theorem algClosedRankOneRootSupportLines_of_centralCover
    (hcover : RankOneCentralCoverStatement.{u}) :
    AlgClosedRankOneRootSupportLinesStatement.{u} := by
  intro k _ _ G hG T hT i hi J P hP hdep r
  have := hG.isAffineHom
  have := hG.smooth
  have hα : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  obtain ⟨C, hC, f, t, hf, ht, hsq⟩ :=
    hcover k G hG T hT i hi ⟨P.root r, hα⟩ hdep
  have := hf.isAffineHom_source
  have := hf.locallyOfFiniteType_source
  refine ⟨fun β hβ => eq_or_eq_neg_of_sl2_centralCover hT i C hC f hf t ht hsq hβ hα,
    ⟨RankOneCentralCover.rootLineOfCover_isogeny C hC hT i f hf t ht hsq (P.root r) hα⟩,
    ⟨RankOneCentralCover.rootLineOfCover_isogeny C hC hT i f hf t ht hsq
      (-P.root r) (hP.neg_mem_roots hα)⟩⟩

/-- Pointwise root support and actual root-space lines give the exact cell proposition. -/
theorem splitRankOneRootCell_of_supportLines
    (hstruct : SplitRankOneRootSupportLinesStatement.{u}) :
    SplitRankOneRootCellStatement.{u} := by
  intro k _ G hG T hT i hi J P hP hdep r
  have := hG.isAffineHom
  obtain ⟨hsupport, hline, hnegline⟩ := hstruct k G hG T hT i hi J P hP hdep r
  obtain ⟨xp, xm, hc⟩ := LocalRankOneRootCell.exists_rootCell_of_support_lines
    hG hT i hi P hP hdep r hsupport hline hnegline
  exact ⟨xp, xm, hc.conj_xp, hc.conj_xm, hc.isOpenImmersion, hc.exists_iff, hc.mul_eq⟩

/-- The original arbitrary-field root-cell proposition reduces to the geometric cover. -/
theorem splitRankOneRootCell_of_centralCover
    (hcover : RankOneCentralCoverStatement.{u}) :
    SplitRankOneRootCellStatement.{u} :=
  splitRankOneRootCell_of_supportLines
    (splitRankOneRootSupportLines_of_algClosed
      (algClosedRankOneRootSupportLines_of_centralCover hcover))

/-- Choose actual root-cell parametrizations from the supplied geometric cover theorem. -/
def rootCellParametrizationsOfCentralCover
    (hcover : RankOneCentralCoverStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (r : J) :
    { p : (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G) ×
        (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G) //
      RootCell.IsRootCell i (P.root r) (P.coroot r) p.1 p.2 } := by
  have := hG.isAffineHom
  let hstruct := splitRankOneRootSupportLines_of_algClosed
    (algClosedRankOneRootSupportLines_of_centralCover hcover)
  have hs := hstruct k G hG T hT i hi J P hP hdep r
  exact LocalRankOneRootCell.parametrizationsOfSupportLines hG hT i hi P hP hdep r
    hs.1 hs.2.1 hs.2.2

end Langlands.GroupScheme
