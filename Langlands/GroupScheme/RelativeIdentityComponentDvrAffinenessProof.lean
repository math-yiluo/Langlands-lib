import Langlands.GroupScheme.RelativeIdentityComponentDvrAffinenessStatement
import Langlands.GroupScheme.RelativeIdentityComponentFiberComparison
import Langlands.AlgebraicGeometry.SmoothDvrAffineOpenGeometry

/-! # Affineness of smooth relative identity components over arbitrary DVRs -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- Every actual relative identity component of a smooth affine group scheme
is affine over an arbitrary discrete valuation ring. -/
theorem smoothDvrAffineness : SmoothDvrAffinenessStatement.{u} := by
  intro R _ _ _ G hsm ha H i hi
  have : Smooth G.X.hom := hsm
  have : IsAffineHom G.X.hom := ha
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let U : G.X.left.Opens := i.hom.hom.left.opensRange
  have hU : IsAffineOpen U := by
    apply Langlands.AlgebraicGeometry.SmoothDvrAffineOpenGeometry.isAffineOpen_of_fiberwise_closed
      R G.X.left G.X.hom U
    exact isClosed_fiber_preimage_range_inclusion G i hi
  have : IsAffine U := hU
  have : IsAffine H.X.left := IsAffine.of_isIso
    (IsOpenImmersion.isoOfRangeEq i.hom.hom.left U.ι (by simp [U])).hom
  infer_instance

end Langlands.GroupScheme.RelativeIdentityComponent
