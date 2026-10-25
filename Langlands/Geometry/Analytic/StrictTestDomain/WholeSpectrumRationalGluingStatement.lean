import Langlands.Geometry.Analytic.StrictTestDomain.RationalLimits

/-! # Scalar rational descent over the whole spectrum -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- Compatible scalar sections on a finite rational covering of the whole
spectrum uniquely descend to the presented strict affinoid base algebra. -/
def WholeSpectrumRationalGluingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K)
    (I : Type u) [Finite I] (D : I → RationalData K P),
    (∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) →
    ∀ s : ∀ i, (D i).algebra,
      (∀ i j, (interLeft (D i) (D j)).restriction (s i) =
        (interRight (D i) (D j)).restriction (s j)) →
      ∃! a : P, ∀ i, (D i).baseMap a = s i

end Langlands.Analytic.StrictTestDomain
