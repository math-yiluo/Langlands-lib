import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.Decomposition
import Mathlib.GroupTheory.DoubleCoset

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-! # The endpoints of standard parabolics -/

/-- The minimal-parabolic/torus-centralizer endpoint and the full-group endpoint. -/
def StandardParabolicEndpointsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      standardParabolic i ν ∅ = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ∧
      standardLevi i ν ∅ = torusCentralizer i ∧
      standardParabolic i ν (simpleRelativeRoots i ν) = ⊤ ∧
      standardLevi i ν (simpleRelativeRoots i ν) = ⊤ ∧
      standardUnipotent i ν (simpleRelativeRoots i ν) = ⊥

end Langlands.GroupScheme
