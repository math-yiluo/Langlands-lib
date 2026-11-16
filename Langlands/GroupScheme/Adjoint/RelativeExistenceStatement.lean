import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: affine full-centre quotients over an arbitrary base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every reductive group scheme over an arbitrary scheme has an affine fppf
quotient by its full scheme-theoretic centre. This is the quotient-existence
consequence of Conrad, Theorem 3.3.4 and Corollary 3.3.5, used separately from
the stronger assertions about the reductivity and centre of the quotient. -/
def RelativeAdjointQuotientExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (A : GroupScheme S) (q : G ⟶ A),
      IsAffineHom A.X.hom ∧ RelativeRoot.IsFppfQuotient (center G) q

end Langlands.GroupScheme
