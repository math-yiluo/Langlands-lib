import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.SplitTorus

/-! # A maximal split torus of a derived subgroup inside an ambient maximal split torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over any field, an ambient maximal split torus contains a maximal split torus of
the actual scheme-theoretic derived subgroup of a connected reductive group. -/
def DerivedMaximalSplitTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsConnectedReductive G → IsDerivedSubgroup d →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∃ (S_D : CommGroupScheme (Spec (CommRingCat.of k))) (j : S_D.toGrp ⟶ D)
        (e : S_D ⟶ S),
        IsMaximalSplitTorus j ∧
        IsClosedSubgroup (CommGroupScheme.groupHom e) ∧
        j ≫ d = CommGroupScheme.groupHom e ≫ i

end Langlands.GroupScheme
