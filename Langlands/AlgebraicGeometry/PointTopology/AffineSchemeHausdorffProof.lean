import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeHausdorffStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Proof of the Hausdorff criterion from the actual affine-line origin
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [TopologicalSpace S] [IsTopologicalRing S]

/-- Under line normalization the actual origin has closed point image exactly
when the value ring is Hausdorff. -/
theorem isClosed_range_affineLineOrigin_iff
    (T : AffineSchemeTopologyFamily R S) (hT : AffineSchemeTopologyLine R S T) :
    @IsClosed (RingPoint R (ringTest R (MvPolynomial Unit R)) S)
      (T (ringTest R (MvPolynomial Unit R)))
      (Set.range (fun p : RingPoint R (ringTest R R) S => p ≫ affineLineOrigin R)) ↔
        T2Space S := by
  let : TopologicalSpace (RingPoint R (ringTest R (MvPolynomial Unit R)) S) :=
    T (ringTest R (MvPolynomial Unit R))
  have hLine : IsHomeomorph (affineLinePointEquiv R S) := hT
  erw [range_affineLineOrigin_points R S]
  exact (hLine.homeomorph _).isClosed_preimage.trans
    IsTopologicalAddGroup.t2Space_iff_zero_closed.symm

/-- Test the closed-embedding requirement on the actual closed immersion of
the origin into the affine line. -/
theorem t2Space_of_affineSchemeTopologyClosedEmbeddings
    (T : AffineSchemeTopologyFamily R S) (hT : AffineSchemeTopologyLine R S T)
    (hclosed : AffineSchemeTopologyClosedEmbeddings R S T) : T2Space S := by
  let : TopologicalSpace (RingPoint R (ringTest R R) S) := T (ringTest R R)
  let : TopologicalSpace (RingPoint R (ringTest R (MvPolynomial Unit R)) S) :=
    T (ringTest R (MvPolynomial Unit R))
  have horigin := hclosed (ringTest R R) (ringTest R (MvPolynomial Unit R))
    (affineLineOrigin R)
  exact (isClosed_range_affineLineOrigin_iff R S T hT).mp horigin.isClosed_range

theorem affineSchemeHausdorffCriterion : AffineSchemeHausdorffCriterion R S := by
  refine ⟨isClosed_range_affineLineOrigin_iff R S,
    t2Space_of_affineSchemeTopologyClosedEmbeddings R S, ?_⟩
  constructor
  · intro hclosed
    apply t2Space_of_affineSchemeTopologyClosedEmbeddings R S
      (evaluationAffineSchemeTopologyFamily R S) _ hclosed
    exact (affineLinePointHomeomorph R S).isHomeomorph
  · intro hT2
    let : T2Space S := hT2
    intro X Y _ _ _ _ f _
    exact isClosedEmbedding_affineSchemePointMap R S f

end Langlands.AlgebraicGeometry.PointTopology
