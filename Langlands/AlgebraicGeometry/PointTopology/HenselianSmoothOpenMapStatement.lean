import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Openness of smooth maps on rational points over Henselian ultrametric fields

This proposition uses Henselianity of the norm valuation ring, without a completeness
assumption. The point carriers, morphisms, smoothness and evaluation topologies are the
published ones.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A smooth morphism of affine schemes over a nontrivially normed ultrametric field
with Henselian norm valuation ring induces an open map for `rationalPointTopology`. -/
def HenselianSmoothRationalPointOpenMapStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]
    (X Y : Over (Spec (CommRingCat.of K))) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [Smooth f.left],
    letI : TopologicalSpace (RationalPoint K X) := rationalPointTopology K X
    letI : TopologicalSpace (RationalPoint K Y) := rationalPointTopology K Y
    IsOpenMap (fun p : RationalPoint K X => p ≫ f)

end Langlands.AlgebraicGeometry.PointTopology
