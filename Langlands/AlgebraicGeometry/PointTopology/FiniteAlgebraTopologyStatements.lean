import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.RingTheory.Finiteness.Projective

/-! # The topology of a finite projective ring extension -/

noncomputable section

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A finite projective ring extension carries a canonical topological-ring
structure for which its coefficient inclusion is a split linear embedding. -/
def FiniteProjectiveAlgebraTopologyProperties
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (S : Type*) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Projective R S] [FaithfulSMul R S] : Prop :=
  letI : TopologicalSpace S := moduleTopology R S
  IsTopologicalRing S ∧
    ∃ (l : S →ₗ[R] R), Function.LeftInverse l (algebraMap R S) ∧
      Continuous l ∧ IsEmbedding (algebraMap R S)

end Langlands.AlgebraicGeometry.PointTopology
