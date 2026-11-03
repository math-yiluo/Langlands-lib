import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Base change of actual homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding.HomogeneousQuotient

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
variable {G H : GroupScheme S} {i : H ⟶ G} (Q : HomogeneousQuotient i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual homogeneous quotient remains such a quotient after arbitrary base change. -/
def baseChange : HomogeneousQuotient ((GroupScheme.baseChange b).map i) where
  scheme := (Over.pullback b).obj Q.scheme
  projection := (Over.pullback b).map Q.projection
  separated := by
    let := Q.separated
    change IsSeparated (pullback.snd Q.scheme.hom b)
    infer_instance
  locallyOfFiniteType := by
    let := Q.locallyOfFiniteType
    change LocallyOfFiniteType (pullback.snd Q.scheme.hom b)
    infer_instance
  quasiCompact := by
    let := Q.quasiCompact
    change QuasiCompact (pullback.snd Q.scheme.hom b)
    infer_instance
  smooth_projection :=
    MorphismProperty.overPullbackMap (P := @Smooth) b Q.projection Q.smooth_projection
  surjective_projection :=
    MorphismProperty.overPullbackMap (P := @Surjective) b Q.projection Q.surjective_projection
  quasiCompact_projection :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) b Q.projection Q.quasiCompact_projection
  fibers := by
    intro T g h
    rw [← ((Over.mapPullbackAdj b).homEquiv T Q.scheme).symm.injective.eq_iff,
      (Over.mapPullbackAdj b).homEquiv_naturality_right_symm g Q.projection,
      (Over.mapPullbackAdj b).homEquiv_naturality_right_symm h Q.projection]
    change baseChangePointsEquiv b G T g ≫ Q.projection =
        baseChangePointsEquiv b G T h ≫ Q.projection ↔ _
    rw [Q.fibers, SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
      map_mul, map_inv]

/-- The base-changed projection commutes with the maps to the original schemes. -/
@[reassoc (attr := simp)]
theorem baseChange_projection_fst :
    (Q.baseChange b).projection.left ≫ pullback.fst Q.scheme.hom b =
      pullback.fst G.X.hom b ≫ Q.projection.left := by
  change ((Over.pullback b).map Q.projection).left ≫ _ = _
  simp only [Over.pullback_map_left, pullback.lift_fst]

/-- Affineness of the actual quotient is preserved by arbitrary base change. -/
theorem baseChange_isAffineHom (hQ : IsAffineHom Q.scheme.hom) :
    IsAffineHom (Q.baseChange b).scheme.hom := by
  change IsAffineHom (pullback.snd Q.scheme.hom b)
  exact isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback Q.scheme.hom b) hQ

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding.HomogeneousQuotient
