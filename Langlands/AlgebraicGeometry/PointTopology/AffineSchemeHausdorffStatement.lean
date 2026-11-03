import Langlands.AlgebraicGeometry.PointTopology.AffineLineOrigin
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyAxioms

/-!
# The Hausdorff criterion from the actual affine-line origin
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The strengthened closed-immersion requirement for actual finite-type
affine schemes: the maps on points must be closed embeddings. -/
def AffineSchemeTopologyClosedEmbeddings
    (T : AffineSchemeTopologyFamily R S) : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of R))) [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsClosedImmersion f.left],
    @IsClosedEmbedding (RingPoint R X S) (RingPoint R Y S) (T X) (T Y)
      (fun p => p ≫ f)

/-- The actual origin detects Hausdorffness for any affine-line-normalized
topology family. Consequently the strengthened closed-immersion requirement
forces Hausdorffness, and for the canonical evaluation family it is equivalent
to Hausdorffness. -/
def AffineSchemeHausdorffCriterion
    [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  (∀ T : AffineSchemeTopologyFamily R S, AffineSchemeTopologyLine R S T →
    (@IsClosed (RingPoint R (ringTest R (MvPolynomial Unit R)) S)
      (T (ringTest R (MvPolynomial Unit R)))
      (Set.range (fun p : RingPoint R (ringTest R R) S => p ≫ affineLineOrigin R)) ↔
        T2Space S)) ∧
  (∀ T : AffineSchemeTopologyFamily R S, AffineSchemeTopologyLine R S T →
    AffineSchemeTopologyClosedEmbeddings R S T → T2Space S) ∧
  (AffineSchemeTopologyClosedEmbeddings R S (evaluationAffineSchemeTopologyFamily R S) ↔
    T2Space S)

end Langlands.AlgebraicGeometry.PointTopology
