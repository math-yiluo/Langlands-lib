import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.Decomposition
import Mathlib.GroupTheory.DoubleCoset

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-! # The order on standard parabolics -/

/-- Inclusion and injectivity of standard parabolics, and the corresponding Levi and unipotent inclusions. -/
def StandardParabolicOrderStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      (∀ J K : Set (characterLattice T),
        J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν →
          (J ⊆ K ↔ standardParabolic i ν J ≤ standardParabolic i ν K) ∧
          (J ⊆ K → standardLevi i ν J ≤ standardLevi i ν K ∧
            standardUnipotent i ν K ≤ standardUnipotent i ν J)) ∧
      Function.Injective (fun J : {J : Set (characterLattice T) //
        J ⊆ simpleRelativeRoots i ν} => standardParabolic i ν J.1)

end Langlands.GroupScheme
