import Langlands.GroupScheme.Reductive.RankOneCentralCoverStatement
import Langlands.GroupScheme.Reductive.RankOneCentralCoverLines
import Langlands.GroupScheme.Reductive.CentralCoverRootOpposition
import Langlands.GroupScheme.Reductive.RootLieLineRankOneReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Reductive.RankOnePositiveRootBaseChange
import Langlands.GroupScheme.Torus.WeightSpaceScalarExtension
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Split root lines from an independent geometric rank-one central cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace RankOneCentralCover

/-- A supplied geometric rank-one cover theorem gives every actual rank-one
root-space line over the original arbitrary field. -/
theorem nonempty_rootLine_of_rankOneCover
    (hcover : RankOneCentralCoverStatement.{u})
    (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ mu ∈ roots i, ∀ nu ∈ roots i, ¬ LinearIndependent ℤ ![mu, nu])
    (chi : characterLattice T) (hchi : haveI := hG.isAffineHom; chi ∈ roots i) :
    haveI := hG.isAffineHom
    Nonempty (k ≃ₗ[k] weightSpace i chi) := by
  have := hG.isAffineHom
  have := hG.smooth
  let b := toAlgebraicClosure k
  let Gc := (GroupScheme.baseChange b).obj G
  let Tc := (CommGroupScheme.baseChange b).obj T
  let ic : Tc.toGrp ⟶ Gc := (GroupScheme.baseChange b).map i
  let chic := characterLattice.baseChange b T chi
  have hGc : IsConnectedReductive Gc := hG.baseChange_toAlgebraicClosure
  have := hGc.isAffineHom
  have hic : IsMaximalTorus ic :=
    (maximalTorusBaseChange k (AlgebraicClosure k) G T i hi.1 hi.2.1).mp hi
  have hdepc : ∀ mu ∈ roots ic, ∀ nu ∈ roots ic,
      ¬ LinearIndependent ℤ ![mu, nu] :=
    (roots_pairwise_dependent_baseChange_iff
      (K := AlgebraicClosure k) G T hT i).mpr hdep
  have hchic : chic ∈ roots ic :=
    (mem_roots_baseChange_iff (K := AlgebraicClosure k) G T hT i chi).mpr hchi
  obtain ⟨C, hC, f, t, hf, ht, hsq⟩ :=
    hcover (AlgebraicClosure k) Gc hGc Tc (hT.baseChange b) ic hic
      ⟨chic, hchic⟩ hdepc
  have := hf.isAffineHom_source
  have := hf.locallyOfFiniteType_source
  have hline : Nonempty (AlgebraicClosure k ≃ₗ[AlgebraicClosure k]
      weightSpace ic chic) :=
    ⟨rootLineOfCover_isogeny C hC (hT.baseChange b) ic f hf t ht hsq chic hchic⟩
  exact (weightSpace_line_baseChange_iff
    (K := AlgebraicClosure k) hT i chi).mp hline

/-- Choose coordinates on an actual rank-one root space from the supplied
geometric cover theorem, after reflecting the line through scalar extension. -/
def rootLineOfRankOneCover
    (hcover : RankOneCentralCoverStatement.{u})
    (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ mu ∈ roots i, ∀ nu ∈ roots i, ¬ LinearIndependent ℤ ![mu, nu])
    (chi : characterLattice T) (hchi : haveI := hG.isAffineHom; chi ∈ roots i) :
    haveI := hG.isAffineHom
    k ≃ₗ[k] weightSpace i chi :=
  Classical.choice (nonempty_rootLine_of_rankOneCover
    hcover k G hG T hT i hi hdep chi hchi)

end RankOneCentralCover

/-- The exact split root-line proposition follows from the single retained
geometric central-cover premise. -/
theorem splitRootLieLine_of_centralCover
    (hcover : RankOneCentralCoverStatement.{u}) : SplitRootLieLineStatement.{u} := by
  apply splitRootLieLine_of_rankOne dynamicCentralizerReductive
  intro k _ G hG T hT i hi hdep chi hchi
  exact RankOneCentralCover.nonempty_rootLine_of_rankOneCover
    hcover k G hG T hT i hi hdep chi hchi

end Langlands.GroupScheme
