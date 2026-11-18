import Langlands.GroupScheme.Reductive.ConnectedFramedIsomorphism
import Langlands.GroupScheme.Reductive.RootWeightLineBundles
import Langlands.GroupScheme.Reductive.ConnectedPicardAffineConjugacy
import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismTheoremProof
import Langlands.GroupScheme.Reductive.SplitTorusBorelIsomorphismStatement

/-! # Isomorphisms and conjugacy over a connected Picard-trivial base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- Conrad's Proposition 6.2.11(2), with the exact scheme-line-bundle Picard hypothesis. -/
theorem reductiveSplitTorusBorelIsomorphism :
    ReductiveSplitTorusBorelIsomorphismStatement.{u} := by
  classical
  have hAffine : AffinePinnedIsomorphismTheoremStatement.{u} :=
    affinePinnedIsomorphismTheorem
  intro S hS hPic
  let : ConnectedSpace S := hS
  constructor
  · intro G H hG hH hloc I I' _ _ t t' ht hmax ht' hmax'
    let : Fintype I := Fintype.ofFinite I
    let : Fintype I' := Fintype.ofFinite I'
    let := hG.isAffineHom
    let := hH.isAffineHom
    obtain ⟨J, P, hP⟩ :=
      exists_globalCoordinateRootDatumOf_of_connected I G hG t hmax
    obtain ⟨J', Q, hQ⟩ :=
      exists_globalCoordinateRootDatumOf_of_connected I' H hH t' hmax'
    let : Finite J := hP.1
    let : Finite J' := hQ.1
    let : Fintype J := Fintype.ofFinite J
    let : Fintype J' := Fintype.ofFinite J'
    let F := CoordinateRootDatum.picardRootFrames hG t hmax P hP hPic
    let F' := CoordinateRootDatum.picardRootFrames hH t' hmax' Q hQ hPic
    have hF : CoordinateRootDatum.AffineRootFrames.IsCoherent t P F :=
      CoordinateRootDatum.picardRootFrames_isCoherent hG t hmax P hP hPic
    have hF' : CoordinateRootDatum.AffineRootFrames.IsCoherent t' Q F' :=
      CoordinateRootDatum.picardRootFrames_isCoherent hH t' hmax' Q hQ hPic
    constructor
    · let d := CoordinateRootDatum.torusIsoOfEtaleLocalIsoOfCoherentFrames
        t t' P Q hG ht hmax hP hH ht' hmax' hQ F hF F' hF' hAffine hloc
      exact ⟨d.val, d.property⟩
    · intro B B' i i' hi hi' hti hti'
      let d := CoordinateRootDatum.torusBorelIsoOfEtaleLocalIsoOfCoherentFrames
        t t' P Q hG ht hmax hP hH ht' hmax' hQ F hF F' hF' hAffine hloc
        i i' hi hi' hti hti'
      exact ⟨d.iso, d.torus_range, d.borel_range⟩
  · intro hSaff
    let : IsAffine S := hSaff
    intro G hG I I' _ _ t t' ht hmax ht' hmax'
    exact connectedPicardAffineSplitTorusBorelConjugacy
      S hPic G hG I I' t t' ht hmax ht' hmax'

end Langlands.GroupScheme
