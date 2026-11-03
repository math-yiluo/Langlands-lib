import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: two Borel subgroups contain a common ambient maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Two Borel subgroups of a connected reductive group over an algebraically closed field
contain a common maximal torus of the ambient group (Borel–Tits 1965, §2.4). -/
def TwoBorelCommonMaximalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (B B' : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (i' : B' ⟶ G),
      IsBorelSubgroup i → IsBorelSubgroup i' →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
        (f : T.toGrp ⟶ B) (f' : T.toGrp ⟶ B'),
        IsMaximalTorus t ∧ f ≫ i = t ∧ f' ≫ i' = t

end Langlands.GroupScheme
