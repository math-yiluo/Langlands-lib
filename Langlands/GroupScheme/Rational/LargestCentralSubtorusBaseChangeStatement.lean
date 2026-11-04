import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Largest central subtori of reductive groups under field extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a connected reductive group over a field, a largest central subtorus
remains a largest central subtorus after every extension of the base field. -/
def ReductiveLargestCentralSubtorusBaseChangeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (Z : CommGroupScheme (Spec (CommRingCat.of k))) (z : Z.toGrp ⟶ G),
    IsConnectedReductive G → IsLargestCentralSubtorus z →
      IsLargestCentralSubtorus
        (Z := (CommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj Z)
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map z)

end Langlands.GroupScheme
