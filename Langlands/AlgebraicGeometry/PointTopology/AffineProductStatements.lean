import Langlands.AlgebraicGeometry.PointTopology.AffineProducts
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Product topology and canonical projection statements for affine points
-/

noncomputable section

universe u v w x

open CategoryTheory CategoryTheory.Limits Topology
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Over a topological value ring, tensor-point restriction has the product topology. -/
def TensorProductTopologyProperty
    (R : Type u) (A : Type v) (B : Type w) (S : Type x)
    [CommRing R] [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  IsHomeomorph (AlgPoint.tensorPointPair : AlgPoint R (A ⊗[R] B) S →
    AlgPoint R A S × AlgPoint R B S)

section SchemeProducts

open _root_.AlgebraicGeometry

variable (R A B S : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R A] [Algebra R B] [Algebra R S]

/-- The affine comparison is the map given by the actual scheme pullback projections. -/
def SpecProductProjectionProperty : Prop :=
  ∀ p : SpecProductPoint R A B S,
    ((specProductPointPairEquiv R A B S) p).1.1 =
        p.1 ≫ pullback.fst (Spec.algebraMap R A) (Spec.algebraMap R B) ∧
      ((specProductPointPairEquiv R A B S) p).2.1 =
        p.1 ≫ pullback.snd (Spec.algebraMap R A) (Spec.algebraMap R B)

/-- The actual scheme product-point comparison has the product topology. -/
def SpecProductTopologyProperty [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  IsHomeomorph (specProductPointPairEquiv R A B S)

/-- Canonical projection identification and product-topology compatibility. -/
def AffineProductProperties [TopologicalSpace S] : Prop :=
  SpecProductProjectionProperty R A B S ∧
    (∀ [IsTopologicalRing S], TensorProductTopologyProperty R A B S) ∧
    (∀ [IsTopologicalRing S], SpecProductTopologyProperty R A B S)

end SchemeProducts

end Langlands.AlgebraicGeometry.PointTopology
