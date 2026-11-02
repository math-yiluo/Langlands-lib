import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveAffineDescentStatement

/-! # Transfer of finite-surjective affine descent to algebraic spaces

The presentation form `EtaleEquivalenceRelationAffineDescentStatement` implies Stacks
Project Lemma 70.15.1 (Tag 07VS) for the Library's algebraic spaces over a base scheme.
-/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Finite-surjective descent of affineness for étale equivalence relations implies
finite-surjective descent of affineness for algebraic spaces over any base scheme, in the
same universe. -/
def EtaleEquivalenceRelationAffineDescentTransferStatement : Prop :=
  EtaleEquivalenceRelationAffineDescentStatement.{u} →
    AlgebraicSpace.FiniteSurjectiveAffineDescentStatement.{u}

end Langlands.AlgebraicGeometry
