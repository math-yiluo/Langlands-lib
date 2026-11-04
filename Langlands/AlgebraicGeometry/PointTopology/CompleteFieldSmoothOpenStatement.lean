import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Analysis.Normed.Field.Basic

/-! # Smooth maps on points over complete nontrivially normed fields -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Conrad's local openness assertion, with the actual affine-chart point topologies. -/
def CompleteFieldSmoothPointOpenStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (X Y : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Smooth f.left],
      letI : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
      letI : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
      IsOpenMap (X := RingPoint K X K) (Y := RingPoint K Y K)
        (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K))

end Langlands.AlgebraicGeometry.PointTopology
