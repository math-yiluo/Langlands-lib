import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.Decomposition
import Mathlib.GroupTheory.DoubleCoset

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-! # Standard parabolics inside standard Levis -/

/-- The all-test semidirect decomposition of a nested Levi–parabolic intersection and the rational unipotent product. -/
def StandardLeviIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ J K : Set (characterLattice T),
        J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν → J ⊆ K →
        (∀ Q : Over (Spec (CommRingCat.of k)),
          let H := (standardLevi i ν K ⊓ standardParabolic i ν J).carrier Q
          let V := (standardLevi i ν K ⊓ standardUnipotent i ν J).carrier Q
          let L := (standardLevi i ν J).carrier Q
          V ≤ H ∧ L ≤ H ∧ (V.subgroupOf H).Normal ∧
            (V.subgroupOf H).IsComplement' (L.subgroupOf H)) ∧
        (↑(standardUnipotentPoints i ν J) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
          (↑(standardLeviPoints i ν K ⊓ standardUnipotentPoints i ν J) :
            Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) *
            (↑(standardUnipotentPoints i ν K) :
              Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))

end Langlands.GroupScheme
