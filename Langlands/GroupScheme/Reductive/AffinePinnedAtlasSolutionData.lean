import Langlands.GroupScheme.Reductive.AffinePinnedAtlasSolutionTorus

/-! # Relative quasi-split data in actual pinned atlas solutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedAtlas

open Descent Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} (A : AffinePinnedAtlas G)
    (P : RelativePinnedComparison.{u}) (s : Solution (A.datum P))

/-- Every actual solution of the corrected pinned atlas carries a Borel
containing a closed fibrewise maximal relative torus. -/
def relativeQuasiSplitTorusData (hG : IsReductive G) :
    RelativeQuasiSplitTorusData s.obj := by
  apply Classical.choice
  let hred := A.solution_isReductive P s hG
  let : IsAffineHom s.obj.X.hom := hred.isAffineHom
  let : Smooth s.obj.X.hom := hred.smooth
  let χ := A.descendedCocharacter P s
  obtain ⟨B, j, hjclosed, _, hj⟩ := (dynamicBaseRepresentability S s.obj χ).1
  obtain ⟨Z, z, hzclosed, _, hz⟩ := (dynamicBaseRepresentability S s.obj χ).2.2
  have hZ := A.isTorus_descendedCocharacter P s z hz
  let T := hZ.commGroupScheme
  refine ⟨{
    reductive := hred
    borel := ⟨B, j, A.isRelativeBorel_descendedCocharacter P s j hG hjclosed hj⟩
    torus := T
    torusInclusion := z
    torusIsTorus := hZ
    torusClosed := hzclosed
    torusMaximal := A.isFibrewiseMaximalTorus_descendedCocharacter P s
      (T := T) z hzclosed hz
    torus_le_borel := ?_ }⟩
  change SubgroupFunctor.range z ≤ SubgroupFunctor.range j
  rw [hz.2, hj.2]
  exact centralizer_le_parabolic χ

end Langlands.GroupScheme.AffinePinnedAtlas
