import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCategory

/-! # Rational representation against arbitrary positive-radius affinoid tests -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- Every actual rational chart represents its closed inequality locus against
all finite positive-polyradius affinoid tests. No spectral criterion, fraction
solution, monomial bound or factorization is supplied as an extra hypothesis. -/
def RationalRepresentationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (d : RationalChart K A),
    Represents K d.baseMap d.locus

end Langlands.Analytic.PresentedAffinoidAlgebra
