import Langlands.AlgebraicGeometry.DvrAffineReducedFibreStatement
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.ConditionalReduction
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeReducedFibreProof
import Langlands.CommutativeAlgebra.CompleteLocalNormalizationFinitenessProof

/-! # Proof of the affine reduced fibre theorem over a discrete valuation ring -/

universe u

namespace Langlands.AlgebraicGeometry

/-- Proof of `DvrAffineReducedFibreStatement`: the conditional reduction
`DvrAffineReducedFibre.dvrAffineReducedFibreConditional` applied to the proofs of its two
premises, universal Japanese finiteness over complete local rings and the scheme reduced fibre
theorem (at equal universes). -/
theorem dvrAffineReducedFibre : DvrAffineReducedFibreStatement.{u} :=
  DvrAffineReducedFibre.dvrAffineReducedFibreConditional
    CommutativeAlgebra.completeLocalNormalizationFiniteness
    DvrAffineReducedFibre.schemeReducedFibre.{u, u}

end Langlands.AlgebraicGeometry
