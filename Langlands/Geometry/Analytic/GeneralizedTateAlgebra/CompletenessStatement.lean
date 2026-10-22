import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Definitions

/-! # Completeness target for positive-polyradius restricted power series -/

universe u v

namespace Langlands.Analytic.GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ) (K : Type v)
  [NormedCommRing K] [IsUltrametricDist K]

/-- The actual weighted Gauss norm is complete whenever the coefficient ring is. -/
def CompletenessStatement [CompleteSpace K] : Prop :=
  CompleteSpace (GeneralizedTateAlgebra r K)

end Langlands.Analytic.GeneralizedTateAlgebra
