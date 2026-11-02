import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineDescentStatement
import Langlands.AlgebraicGeometry.NoetherianEtaleEquivalenceRelationAffineDescentStatement

/-! # Reduction of finite-surjective affine descent to the Noetherian case

The Noetherian approximation step in the proof of Stacks Project Lemma 70.15.1 (Tag 07VS),
in the language of presentations: the Noetherian case implies the general case.
-/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Finite-surjective descent of affineness for étale equivalence relations on Noetherian
affine schemes implies the same descent for étale equivalence relations on all affine
schemes, in the same universe. -/
def EtaleEquivalenceRelationNoetherianApproximationStatement : Prop :=
  NoetherianEtaleEquivalenceRelationAffineDescentStatement.{u} →
    EtaleEquivalenceRelationAffineDescentStatement.{u}

end Langlands.AlgebraicGeometry
