import Langlands.GroupScheme.Descent.EtaleEffectivity
import Langlands.GroupScheme.Reductive.AffinePinnedAtlasSolutionData

/-! # Effective corrected pinned atlas descent and quasi-split torus data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedAtlas

open Descent

variable {S : Scheme.{u}} {G : GroupScheme S} (A : AffinePinnedAtlas G)
    (P : RelativePinnedComparison.{u}) (hG : IsReductive G)

/-- Effective descent of the corrected pinned atlas of a reductive group. -/
def solution : Solution (A.datum P) := by
  letI : IsAffineHom A.group.X.hom := (hG.baseChange A.projection).isAffineHom
  exact (A.datum P).etaleSolution

/-- The resulting group scheme has affine structure morphism. -/
instance solution_isAffineHom : IsAffineHom (A.solution P hG).obj.X.hom := by
  let : IsAffineHom A.group.X.hom := (hG.baseChange A.projection).isAffineHom
  exact inferInstanceAs (IsAffineHom (A.datum P).etaleSolution.obj.X.hom)

/-- A specified Borel containing a closed fibrewise maximal relative torus in
the effective corrected pinned atlas solution. -/
def quasiSplitTorusData : RelativeQuasiSplitTorusData (A.solution P hG).obj :=
  A.relativeQuasiSplitTorusData P (A.solution P hG) hG

/-- The effective corrected pinned atlas solution is relatively quasi-split. -/
theorem solution_isRelativeQuasiSplit : IsRelativeQuasiSplit (A.solution P hG).obj :=
  (A.quasiSplitTorusData P hG).quasiSplit

end Langlands.GroupScheme.AffinePinnedAtlas
