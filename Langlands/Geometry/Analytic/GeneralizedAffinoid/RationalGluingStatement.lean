import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartIntersection

/-! # Scalar rational descent with arbitrary positive radii -/

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

/-- Compatible scalar sections on a finite positive-radius rational covering
of the whole spectrum uniquely descend to the actual affinoid base algebra.
This definition states the analytic descent obligation without assuming it. -/
def WholeSpectrumRationalGluingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K)
    (I : Type v) [Finite I] (D : I → RationalChart K A),
    (∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) →
    ∀ s : ∀ i, (D i).algebra,
      (∀ i j, (interLeft (D i) (D j)).restriction (s i) =
        (interRight (D i) (D j)).restriction (s j)) →
      ∃! a : A, ∀ i, (D i).baseMap a = s i

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
