import Langlands.GroupScheme.Rational.RealCompactPoints
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: compact real points of anisotropic connected reductive groups -/

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A connected reductive real group with split rank zero has compact actual
real points in the canonical regular-evaluation topology. -/
def RealAnisotropicCompactnessStatement : Prop :=
  ∀ G : GroupScheme (Spec (CommRingCat.of ℝ)),
    IsConnectedReductive G → IsAnisotropic G → HasCompactRealPoints G

end Langlands.GroupScheme
