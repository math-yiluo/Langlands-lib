import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Rational.StandardLeviPointComparison

/-! # The inherited point topology on an actual represented standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [TopologicalSpace F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T))
  {M : GroupScheme (Spec (CommRingCat.of F))} (j : M ⟶ G)
  (hj : (standardLevi i ν J).IsRepresentedBy j) (hc : IsClosedSubgroup j)

local instance instStandardLeviPointHomeomorph1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance instStandardLeviPointHomeomorph2 : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- The existing point identification of a closed standard Levi is a
multiplicative homeomorphism for the canonical and subgroup topologies. -/
def standardLeviRationalPointsHomeomorph :
    have : IsClosedImmersion j.hom.hom.left := hc
    have : IsAffine M.X.left := isAffine_of_isAffineHom j.hom.hom.left
    let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
    rationalPoints M ≃ₜ* standardLeviPoints i ν J := by
  have : IsClosedImmersion j.hom.hom.left := hc
  have : IsAffine M.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  exact rationalPointSubgroupHomeomorph F (standardLevi i ν J) j hj hc

@[simp]
theorem standardLeviRationalPointsHomeomorph_toMulEquiv :
    have : IsClosedImmersion j.hom.hom.left := hc
    have : IsAffine M.X.left := isAffine_of_isAffineHom j.hom.hom.left
    let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
    (standardLeviRationalPointsHomeomorph i ν J j hj hc).toMulEquiv =
      standardLeviRationalPointsEquiv i ν J j hj := by
  have : IsClosedImmersion j.hom.hom.left := hc
  have : IsAffine M.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

@[simp]
theorem standardLeviRationalPointsHomeomorph_apply_coe (x : rationalPoints M) :
    (standardLeviRationalPointsHomeomorph i ν J j hj hc x : rationalPoints G) =
      rationalPoints.map j x := rfl

end Langlands.GroupScheme
