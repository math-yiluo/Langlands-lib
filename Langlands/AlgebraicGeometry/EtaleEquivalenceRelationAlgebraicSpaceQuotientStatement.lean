import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Algebraic-space quotients of etale equivalence relations -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace

/-- Every etale equivalence relation over a scheme has an actual fppf
algebraic-space quotient, presented by the original relation. -/
def EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (E : EtaleEquivalenceRelation.{u})
    (b : E.U ⟶ S) (hb : E.t ≫ b = E.s ≫ b),
    let U : Over S := Over.mk b
    let R : Over S := Over.mk (E.t ≫ b)
    let t : R ⟶ U := Over.homMk E.t
    let s : R ⟶ U := Over.homMk E.s hb.symm
    ∃ (Q : AlgebraicSpace S) (a : (schemeYoneda S).obj U ⟶ Q.presheaf),
      IsEtale a ∧ IsSurjective a ∧
        IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a

end Langlands.AlgebraicGeometry
