import Langlands.GroupScheme.MatrixRepresentationProductAnalyticDifferential

/-! # Analytic and algebraic differential comparison for actual matrix representations -/

noncomputable section

universe u

open scoped Matrix Matrix.Norms.Operator

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinearProductDualNumber

variable {J : Type u} [Fintype J]
  {n : J → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  {R : CommRingCat.{u}}
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [Algebra R B]
  {m : Type} [Fintype m] [DecidableEq m]

/-- The independently constructed real Frechet and algebraic dual-number
first-order maps of the same genuine scheme representation agree. -/
def AnalyticProductDifferentialComparison
    (ρ : MatrixRepresentation (groupScheme n R) m) : Prop :=
  ∀ X : ∀ j, Matrix (n j) (n j) B,
    ρ.analyticProductDifferential (B := B) X = ρ.productDifferential B X

end Langlands.GroupScheme.MatrixRepresentation
