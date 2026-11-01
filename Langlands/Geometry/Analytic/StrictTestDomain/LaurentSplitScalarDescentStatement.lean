import Langlands.Geometry.Analytic.StrictTestDomain.ScalarCoverDescent
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentCover

/-! # Degree-zero scalar descent across a Laurent split -/

universe u v

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- Descent on the upper and lower pullback families and separation on the
overlap pullback family imply descent of the original actual rational family. -/
def LaurentSplitScalarDescentStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (I : Type v)
    (D : I → RationalData K P) (f : P),
    ScalarCoverDescent (fun i => (D i).pullback (laurentUpper f).baseMap) →
    ScalarCoverDescent (fun i => (D i).pullback (laurentLower f).baseMap) →
    ScalarCoverSeparated
      (fun i => (D i).pullback ((laurentUpper f).inter (laurentLower f)).baseMap) →
    ScalarCoverDescent D

end Langlands.Analytic.StrictTestDomain
