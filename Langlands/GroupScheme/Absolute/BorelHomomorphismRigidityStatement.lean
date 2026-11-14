import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: homomorphisms agreeing on a Borel subgroup agree -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.21. Let `G` and `G'` be smooth connected affine groups
over an algebraically closed field `k`, let `i : B ⟶ G` be a Borel subgroup and
let `R` be a `k`-algebra. Two homomorphisms `G_R ⟶ G'_R` of group schemes over
`Spec R` that agree on `B_R` are equal. -/
def BorelHomomorphismRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth G'.X.hom] [IsAffineHom G'.X.hom] [ConnectedSpace G'.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
    ∀ (R : Type u) [CommRing R] [Algebra k R],
      let b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k R))
      ∀ (φ₁ φ₂ : (GroupScheme.baseChange b).obj G ⟶ (GroupScheme.baseChange b).obj G'),
        (GroupScheme.baseChange b).map i ≫ φ₁ = (GroupScheme.baseChange b).map i ≫ φ₂ →
          φ₁ = φ₂

end Langlands.GroupScheme
