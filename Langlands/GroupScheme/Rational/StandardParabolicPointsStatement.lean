import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.Decomposition
import Mathlib.GroupTheory.DoubleCoset

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-! # Standard parabolics on rational points -/

/-- The standard Bruhat pieces, subgroup classification, self-normalization and normalizer-induced double-coset bijections. -/
def StandardParabolicPointsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      (∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
        ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          g ∈ standardParabolicPoints i ν J ↔
            ∃ n : normalizerPoints i,
              (QuotientGroup.mk n : relativeWeylGroup i) ∈ standardRelativeWeylGroup i ν J ∧
              ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
                (Over.mk (𝟙 (Spec (CommRingCat.of k)))),
              ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
                (Over.mk (𝟙 (Spec (CommRingCat.of k)))), g = p * n * q) ∧
      (∀ H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
        (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤ H ↔
        ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
          H = standardParabolicPoints i ν J) ∧
      (∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
        Subgroup.normalizer (↑(standardParabolicPoints i ν J) :
              Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) = standardParabolicPoints i ν J) ∧
      ∀ J K : Set (characterLattice T),
        J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν →
        ∃ e : DoubleCoset.Quotient (↑(standardRelativeWeylGroup i ν J) : Set (relativeWeylGroup i))
            (↑(standardRelativeWeylGroup i ν K) : Set (relativeWeylGroup i)) ≃
          DoubleCoset.Quotient (↑(standardParabolicPoints i ν J) :
              Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
            (↑(standardParabolicPoints i ν K) :
              Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)),
          ∀ n : normalizerPoints i,
            e (DoubleCoset.mk (standardRelativeWeylGroup i ν J)
              (standardRelativeWeylGroup i ν K) (QuotientGroup.mk n)) =
              DoubleCoset.mk (standardParabolicPoints i ν J)
                (standardParabolicPoints i ν K) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

end Langlands.GroupScheme
