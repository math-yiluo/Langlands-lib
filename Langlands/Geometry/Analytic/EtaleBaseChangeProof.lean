import Langlands.Geometry.Analytic.EtaleBaseChangeReduction
import Langlands.Geometry.Analytic.FibreProductPullbackProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof

/-! # Étale base change along the glued fibre product -/

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- The second projection of the glued fibre product is étale in the localized category
when the first leg of the original cospan is étale there. -/
theorem etaleBaseChange : EtaleBaseChangeStatement.{u} :=
  etaleBaseChange_of_descent PresentedAffinoidAlgebra.finiteAffinoidAlgebraDescent
    fibreProductPullback

end Langlands.Analytic.SaturatedAtlasPresentation
