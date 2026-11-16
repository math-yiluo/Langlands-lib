import Langlands.GroupScheme.Adjoint.RelativeReductivity
import Langlands.GroupScheme.Adjoint.RelativeExistenceStatement

/-! # Statement: existence of a reductive relative adjoint quotient -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every reductive group scheme over any base has an actual reductive fppf
quotient by its full scheme-theoretic centre. -/
def ReductiveRelativeAdjointQuotientExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (A : GroupScheme S) (q : G ⟶ A), IsRelativeAdjointQuotient q

/-- The published affine quotient existence statement supplies the reductive
quotient as well. -/
theorem ReductiveRelativeAdjointQuotientExistenceStatement.of_affine
    (h : RelativeAdjointQuotientExistenceStatement.{u}) :
    ReductiveRelativeAdjointQuotientExistenceStatement.{u} := by
  intro S G hG
  obtain ⟨A, q, hA, hq⟩ := h S G hG
  let : IsAffineHom A.X.hom := hA
  exact ⟨A, q, hq.isRelativeAdjointQuotient hG⟩

/-- Forget target reductivity to recover the published affine statement. -/
theorem ReductiveRelativeAdjointQuotientExistenceStatement.to_affine
    (h : ReductiveRelativeAdjointQuotientExistenceStatement.{u}) :
    RelativeAdjointQuotientExistenceStatement.{u} := by
  intro S G hG
  obtain ⟨A, q, hq⟩ := h S G hG
  exact ⟨A, q, hq.isReductive_target.isAffineHom, hq.isQuotient⟩

end Langlands.GroupScheme
