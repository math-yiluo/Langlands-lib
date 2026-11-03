import Langlands.GroupScheme.Absolute.Borel

/-! # Geometric structure of the intersection of two rational parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The actual intersection of two rational parabolics is smooth, is
geometrically connected, and geometrically contains an ambient maximal torus.
The pullback is taken in group schemes, without replacing it by its reduction. -/
def ParabolicIntersectionGeometryStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P P' : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G) (j' : P' ⟶ G),
      IsParabolicSubgroup j → IsParabolicSubgroup j' →
      let H := pullback j j'
      let c : H ⟶ G := pullback.fst j j' ≫ j
      let bc := GroupScheme.baseChange (toAlgebraicClosure k)
      Smooth H.X.hom ∧
        ConnectedSpace (bc.obj H).X.left ∧
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
          (f : T.toGrp ⟶ bc.obj H),
          IsMaximalTorus (f ≫ bc.map c)

end Langlands.GroupScheme
