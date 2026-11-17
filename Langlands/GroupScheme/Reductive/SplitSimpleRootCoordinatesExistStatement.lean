import Langlands.GroupScheme.Reductive.SuppliedHighestWeightWordCoordinates

/-! # Full linked simple-root coordinates over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The supplied split pinning admits full linked simple-root coordinates.
This statement retains both entire intrinsic-root functors, opposite torus
equivariance, and the literal rank-one relation on every relative scheme test. -/
def SplitSimpleRootCoordinatesExistStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), Nonempty p.SimpleRootCoordinateFamily

end Langlands.GroupScheme
