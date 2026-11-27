import Langlands.GroupScheme.Rational.InfiniteFieldCenterComparisonStatement
import Langlands.GroupScheme.Reductive.RationalPointDensityProof
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # The scheme center from dense rational points

For a connected reductive group `G` over an infinite field `k`, the full scheme center evaluated
on `k` equals the abstract center of `G(k)`.

The inclusion of the scheme center in the abstract center is `schemeCenterPoints_le_center`.
Conversely, let `z` be central in `G(k)`. Left and right translation by `z` agree after
composition with every rational point. The rational points are Zariski dense
(`reductiveRationalPointDensity`), `G` is reduced because it is smooth, and `G` is separated
because it is affine, so the two translations are equal as morphisms
(`hom_ext_of_denseRationalPoints`). Precomposing this equality of morphisms with an arbitrary
test point, over a possibly nonreduced test scheme, gives the all-test center condition.
-/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- On a reduced separated group over a field, centrality can be detected on
rational points if their images are Zariski dense. -/
theorem RationalCenterComparison.of_denseRationalPoints
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsReduced G.X.left] [IsSeparated G.X.hom]
    (hG : HasDenseRationalPoints k G.X) : RationalCenterComparison G := by
  refine le_antisymm (schemeCenterPoints_le_center G) ?_
  intro z hz
  let t : G.X ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.mkIdTerminal.from G.X
  -- left and right translation by `z` agree as morphisms `G ⟶ G`
  have hcomm : (t ≫ z) * 𝟙 G.X = 𝟙 G.X * (t ≫ z) := by
    apply hom_ext_of_denseRationalPoints hG
    intro p
    have hp : p ≫ t = 𝟙 _ := Over.mkIdTerminal.hom_ext _ _
    simpa only [MonObj.comp_mul, Category.comp_id, ← Category.assoc, hp,
      Category.id_comp] using (Subgroup.mem_center_iff.mp hz p).symm
  -- precompose with an arbitrary test point, over any (possibly nonreduced) test
  intro T a g
  change (a ≫ z) * g = g * (a ≫ z)
  have ha : a = g ≫ t := Over.mkIdTerminal.hom_ext _ _
  have hg := congrArg (g ≫ ·) hcomm
  simpa only [MonObj.comp_mul, Category.comp_id, ← Category.assoc, ← ha] using hg

/-- The scheme center and the abstract center agree on rational points of a
connected reductive group over any infinite field. -/
theorem infiniteFieldCenterComparison : InfiniteFieldCenterComparisonStatement.{u} := by
  intro k _ _ G hG
  let := hG.isAffineHom
  let := hG.smooth
  let := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    k G.X.left G.X.hom
  exact RationalCenterComparison.of_denseRationalPoints G (reductiveRationalPointDensity k G hG)

end Langlands.GroupScheme
