import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyAxioms
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The evaluation topology satisfies the affine axioms
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S]

theorem affineTopologyExistence_proof : AffineTopologyExistenceProperty R S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B _ _ f
    exact AlgPoint.continuous_precomp f.hom
  · intro A B C _ _ _ f g c _ hc
    exact (affinePushoutPointHomeomorph R S c hc).isHomeomorph
  · intro A B _ _ f hf
    exact AlgPoint.isEmbedding_precomp_of_surjective f.hom hf
  · exact ((AlgPoint.polynomialPointHomeomorph (R := R) (S := S) Unit).trans
      (Homeomorph.funUnique Unit S)).isHomeomorph

end Langlands.AlgebraicGeometry.PointTopology
