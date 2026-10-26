import Langlands.Geometry.Analytic.StrictTestDomain.Definitions
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Ordinary denominator localization for trivial-scalar rational quotients -/

universe u

namespace Langlands.Analytic.StrictTestDomain

/-- With trivial scalar norm, the actual rational quotient is a localization
away from its denominator, along its specified bounded structural map. -/
def TrivialScalarRationalLocalizationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K),
    (∀ c : K, ‖c‖ ≤ 1) →
    ∀ d : RationalData K P,
      letI : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
      IsLocalization.Away d.denominator d.algebra

end Langlands.Analytic.StrictTestDomain
