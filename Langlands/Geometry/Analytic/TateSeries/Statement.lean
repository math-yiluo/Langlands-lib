import Langlands.Geometry.Analytic.TateSeries.Definitions

/-! # Exact target for norm-convergent restricted-series expansion -/

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

/-- Over a complete ultrametric coefficient ring, the actual restricted
coefficient monomials sum to the original series in the Gauss norm. -/
def MonomialExpansionStatement : Prop :=
  ∀ (σ : Type u) (K : Type v) [NormedCommRing K] [IsUltrametricDist K]
    [CompleteSpace K] (f : StrictTateAlgebra σ K),
    HasSum (fun d => monomial σ K d (MvPowerSeries.coeff d (series σ K f))) f

end Langlands.Analytic.StrictTateAlgebra
