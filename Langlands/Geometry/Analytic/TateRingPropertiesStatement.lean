import Langlands.Geometry.Analytic.TateAlgebra
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Noetherianity, factoriality and integral closure of strict Tate algebras -/

universe u

namespace Langlands.Analytic.StrictTateAlgebra

/-- The actual finite-variable Tate algebra is a Noetherian domain with
unique factorization and is integrally closed in its fraction ring. -/
def TateRingPropertiesStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ n : ℕ, IsNoetherianRing (StrictTateAlgebra (Fin n) K) ∧
    IsDomain (StrictTateAlgebra (Fin n) K) ∧
    UniqueFactorizationMonoid (StrictTateAlgebra (Fin n) K) ∧
    IsIntegrallyClosed (StrictTateAlgebra (Fin n) K)

end Langlands.Analytic.StrictTateAlgebra
