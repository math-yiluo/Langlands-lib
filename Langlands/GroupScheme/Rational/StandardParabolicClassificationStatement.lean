import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.Decomposition
import Mathlib.GroupTheory.DoubleCoset

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-! # Classification of rational parabolics -/

/-- Classification of dynamic rational parabolics containing the minimal one and uniqueness of the standard conjugacy representative. -/
def StandardParabolicClassificationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      (∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta →
          ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
            Dynamic.parabolic zeta = standardParabolic i ν J) ∧
      ∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        ∃! J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
            Dynamic.parabolic zeta =
              (standardParabolic i ν J.1).comap (G.innerIso g).hom

end Langlands.GroupScheme
