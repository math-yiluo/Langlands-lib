import Langlands.Geometry.Analytic.StrictTestDomain.RationalIdealEffectiveness
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictScalarIdealDescentProof

/-! # Closed-ideal effectiveness on finite full-domain covers -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

/-- Every compatible closed-ideal family on a finite full-domain cover is the
closed extension of its explicit contracted ideal, in the full original scope. -/
theorem idealEffectiveness : IdealEffectivenessStatement.{u} :=
  idealEffectiveness_of_rationalIdealEffectiveness
    (strictScalarIdealDescent StrictTestDomain.strictRationalIdealEffectiveness)

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
