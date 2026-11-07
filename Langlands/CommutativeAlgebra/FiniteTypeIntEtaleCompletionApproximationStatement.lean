import Langlands.CommutativeAlgebra.EtaleCompletionApproximation
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Etale approximation over finite-type integer algebras: statement -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Every maximal localization of a finite-type integer algebra has finite-order
approximation in etale neighbourhoods for maps into its completion. -/
def FiniteTypeIntEtaleCompletionApproximationStatement : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra.FiniteType ℤ S]
    (𝔪 : Ideal S) [𝔪.IsMaximal],
    EtaleCompletionApproximation (Localization.AtPrime 𝔪)

end Langlands.CommutativeAlgebra
