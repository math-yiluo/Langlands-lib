import Langlands.GroupScheme.Reductive.MonomorphismValuativeReductionStatement
import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneralStatement
import Langlands.AlgebraicGeometry.FiniteCoefficientMonomorphismStatement
import Langlands.GroupScheme.Reductive.DirectLimitReductiveStatement

/-! # Finite coefficient reduction of reductive monomorphisms -/

universe u

namespace Langlands.GroupScheme

/-- Homomorphism descent, monicity descent and direct-limit reductivity reduce
the arbitrary-base closed-immersion theorem to locally noetherian bases. -/
def ReductiveMonomorphismNoetherianReductionStatement : Prop :=
  Descent.FiniteCoefficient.HomGeneralStatement.{u} →
  Langlands.AlgebraicGeometry.FiniteCoefficient.MonomorphismStatement.{u} →
  DirectLimitReductiveStatement.{u} →
  (ReductiveMonomorphismValuativeReduction.LocallyNoetherianCase.{u} ↔
    ReductiveMonomorphismClosedImmersionStatement.{u})

end Langlands.GroupScheme
