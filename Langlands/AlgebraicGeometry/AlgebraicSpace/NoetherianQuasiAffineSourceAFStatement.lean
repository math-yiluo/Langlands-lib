import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFStatement

/-! # AF representability from a finite surjection with Noetherian quasi-affine source

The case of `FiniteSurjectiveQuasiAffineSourceAFStatement` in which the underlying topological
space of the source is Noetherian, over an arbitrary base scheme.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Over any base scheme `S`, a quasi-compact quasi-separated algebraic space `Y` with a finite
surjective map from a quasi-affine scheme `U` whose underlying space is Noetherian is represented
by a scheme in which every finite set of points lies in an affine open. -/
def NoetherianQuasiAffineSourceAFStatement : Prop :=
  ∀ (S : Scheme.{u}) (U : Over S) (Y : AlgebraicSpace S) (f : (schemeToSpace S).obj U ⟶ Y),
    IsQuasiCompact Y → IsQuasiSeparated Y → U.left.IsQuasiAffine →
      TopologicalSpace.NoetherianSpace U.left → IsFinite (hom f) → IsSurjective (hom f) →
        ∃ P : Over S, PointTopology.HasFiniteAffineNeighborhoods P.left ∧
          Nonempty ((schemeYoneda S).obj P ≅ Y.presheaf)

end Langlands.AlgebraicGeometry.AlgebraicSpace
