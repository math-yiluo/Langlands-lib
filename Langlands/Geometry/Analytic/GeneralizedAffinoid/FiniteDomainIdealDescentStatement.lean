import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescent

/-! # The finite full-domain closed-ideal effectiveness target -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

/-- Closed-ideal effectiveness on arbitrary finite full-domain covers, expressed
using the explicit ideal of global sections with the prescribed local values. -/
def IdealEffectivenessStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (U : Domain K A) (c : FiniteCover U)
    (I : ∀ i : Fin c.size, Ideal (c.obj i).algebra),
    (∀ i, IsClosed (I i : Set (c.obj i).algebra)) → c.IdealCompatible I →
      ∀ i, (c.map i).restriction.closedIdealMap (c.idealContraction I) = I i

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
