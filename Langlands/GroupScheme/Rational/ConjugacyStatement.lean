import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.InnerAutomorphism

/-! # Conjugacy of maximal split tori and the split rank -/

universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k`, any two maximal split tori `i : T ⟶ G` and `i' : T' ⟶ G` of a connected
reductive group `G` are conjugate by a rational point: there are `g ∈ G(k)` and an isomorphism
`e : T ≅ T'` with `i ≫ int(g) = e ≫ i'`. Moreover every splitting `T ≅ splitTorus S I` of a
maximal split torus has `Nat.card I` equal to the split rank of `G`. -/
def MaximalSplitTorusConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    (∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
        (i' : T'.toGrp ⟶ G), IsMaximalSplitTorus i → IsMaximalSplitTorus i' →
        ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (e : T.toGrp ≅ T'.toGrp),
          i ≫ (G.innerIso g).hom = e.hom ≫ i') ∧
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i → ∀ (I : Type u) [Finite I],
        (T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) → (Nat.card I : ℕ∞) = splitRank G

end Langlands.GroupScheme
