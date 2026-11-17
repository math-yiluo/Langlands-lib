import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain
import Mathlib.RingTheory.RingHom.Flat

/-! # Algebraic flatness of full affinoid-domain restrictions -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

/-- The actual structural map of every full represented affinoid domain is
flat as a homomorphism of its underlying commutative rings. -/
def FlatnessStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (U : Domain K A),
    U.baseMap.toAlgHom.toRingHom.Flat

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
