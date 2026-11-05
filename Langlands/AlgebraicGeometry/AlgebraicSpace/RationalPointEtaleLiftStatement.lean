import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints

/-!
# Lifting rational points of quasi-separated algebraic spaces to étale charts

Every rational point of a quasi-separated algebraic space over a field lifts to a
rational point of an actual affine scheme mapping étale to the space.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Every `k`-point of `X` is the image of a `k`-point of an actual affine scheme
with an étale map to `X`. -/
def RationalPointEtaleLift (k : Type u) [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) : Prop :=
  ∀ x : RingPoints k X k,
    ∃ (U : Over (Spec (CommRingCat.of k))) (f : (schemeToSpace _).obj U ⟶ X),
      IsAffine U.left ∧ IsEtale (hom f) ∧
        ∃ u : RingPoint k U k,
          RingPoints.map f ((schemeRingPointsEquiv k U k).symm u) = x

/-- The rational-point form of Knutson II.6.4 cited by Conrad on printed p.15:
rational points of quasi-separated algebraic spaces over a field lift along
étale maps from affine schemes. -/
def RationalPointEtaleLiftStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k))),
    IsQuasiSeparated X → RationalPointEtaleLift k X

end Langlands.AlgebraicGeometry.AlgebraicSpace
