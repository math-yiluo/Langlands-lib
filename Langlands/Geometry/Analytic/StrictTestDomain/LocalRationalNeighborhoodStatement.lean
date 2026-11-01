import Langlands.Geometry.Analytic.StrictTestDomain.Definitions

/-! # Local rational neighbourhoods of strictly represented subsets -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open Topology

/-- Local Gerritzen–Grauert for presented strict affinoids over a nontrivially
valued field: if an actual affinoid map represents `U` for all presented strict
affinoid tests, then every point of `U` has a unit-radius rational locus of the
ambient spectrum that lies in `U` and is a neighbourhood of the point in the
relative topology of `U`. -/
def LocalRationalNeighborhoodStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    (∃ c : K, 1 < ‖c‖) →
    ∀ (P Q : PresentedStrictAffinoidAlgebra K) (i : BoundedAlgHom K P Q)
      (U : Set (BanachSpectrum P)), Represents K i U →
      ∀ x ∈ U, ∃ d : RationalData K P, d.locus ⊆ U ∧ d.locus ∈ 𝓝[U] x

end Langlands.Analytic.StrictTestDomain
