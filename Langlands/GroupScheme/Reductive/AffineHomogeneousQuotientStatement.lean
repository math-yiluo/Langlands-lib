import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.IdentityComponent

/-! # Reductivity from an affine homogeneous quotient -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth closed subgroup of a connected reductive group has connected
reductive identity component whenever its actual homogeneous quotient is affine.
The quotient has the published smooth surjective projection and exact right-coset
fibers on all scheme tests. -/
def AffineHomogeneousQuotientReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom),
      letI : Smooth H.X.hom := hH
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : IsClosedImmersion i.hom.hom.left := hi
      letI : IsAffineHom H.X.hom := by
        have h : IsAffineHom (i.hom.hom.left ≫ G.X.hom) := inferInstance
        simpa only [Over.w] using h
      ∀ (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i),
        IsAffineHom Q.scheme.hom → IsConnectedReductive (identityComponent H)

end Langlands.GroupScheme
