import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneAmpleStatement
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneLocalFramesProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateGenerationOpenProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof

/-! # Proof: the actual `𝒪(1)` on projective space is ample -/

universe u

namespace Langlands.AlgebraicGeometry

open CategoryTheory _root_.AlgebraicGeometry Langlands.SchemeModule Langlands.Scheme.Modules

/-- For every commutative ring `R` and every `n`, the actual twisting sheaf `twistOne R n`,
bundled with its local rank-one proof, is an ample line bundle on `ProjectiveSpace R n`. Each
point of `D₊(X i)` lies in the generation locus of the coordinate section `X i`, transported
to the first tensor power through `tensorRightUnitor`; that locus is the affine open `D₊(X i)`. -/
theorem projectiveSpaceTwistOneAmple : ProjectiveSpaceTwistOneAmpleStatement.{u} := by
  intro R _ n
  obtain ⟨haff, hsup, hcpt⟩ := projectiveSpaceCoordinateCover R n
  let L : Picard.LineBundle (ProjectiveSpace R n) :=
    ⟨twistOne R n, (projectiveSpaceTwistOneLocalFrames R n).2⟩
  refine ⟨L, rfl, hcpt, fun x => ?_⟩
  have hx : x ∈ (⨆ i, projectiveSpaceCoordinateOpen R n i) := hsup ▸ trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hx
  let s : L.powSections 1 :=
    (tensorRightUnitor (twistOne R n)).inv.app ⊤ (twistOneCoordinate R n i)
  have hs : L.sectionOpen s = projectiveSpaceCoordinateOpen R n i := by
    rw [← projectiveSpaceCoordinateGenerationOpen R n i]
    exact trivializationOpen_mapIso (tensorRightUnitor (twistOne R n)).symm _
  exact ⟨1, le_rfl, s, hs ▸ hi, hs ▸ haff i⟩

end Langlands.AlgebraicGeometry
