import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalCover
import Langlands.Geometry.Analytic.StrictTestDomain.RationalLimits

/-! # Scalar descent on standard rational covers over nontrivially valued fields -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- Over a complete ultrametric field with a scalar of norm greater than one,
compatible scalar sections on the actual standard rational cover of a tuple
without common spectrum zero uniquely descend to the base algebra. -/
def NontrivialStandardRationalGluingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    (∃ c : K, 1 < ‖c‖) →
    ∀ (P : PresentedStrictAffinoidAlgebra K) (n : ℕ) (f : Fin n → P)
      (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0)
      (s : ∀ j : Fin n, (standardRational f hf j).algebra),
      (∀ j l,
        (interLeft (standardRational f hf j) (standardRational f hf l)).restriction (s j) =
          (interRight (standardRational f hf j) (standardRational f hf l)).restriction
            (s l)) →
      ∃! a : P, ∀ j, (standardRational f hf j).baseMap a = s j

end Langlands.Analytic.StrictTestDomain
