import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison
import Mathlib.RingTheory.Noetherian.Defs

/-! # Noetherianity and closed ideals of strict relative unit-radius series -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- Over a complete ultrametric normed field with an element of norm greater
than one, the actual unit-radius relative series algebra in finitely many
variables over a presented strict base is Noetherian, and each of its ideals
is closed for the weighted coefficient norm. -/
def StrictRelativeSeriesPropertiesStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    (∃ c : K, 1 < ‖c‖) →
    ∀ (P : PresentedStrictAffinoidAlgebra K) (m : ℕ),
      IsNoetherianRing
          (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin m)) (ofStrict K P)) ∧
        ∀ I : Ideal
            (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin m)) (ofStrict K P)),
          IsClosed (I : Set
            (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin m)) (ofStrict K P)))

end Langlands.Analytic.PresentedAffinoidAlgebra
