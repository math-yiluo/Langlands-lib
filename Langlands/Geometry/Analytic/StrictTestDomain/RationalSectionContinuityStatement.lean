import Langlands.Geometry.Analytic.StrictTestDomain.RationalStabilizerAction
import Mathlib.Topology.Algebra.Group.Basic

/-! # Continuity target for fixed rational-quotient section orbits -/

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory

/-- Norm-continuous base-algebra orbits induce norm-continuous section orbits
on every fixed unit-radius rational quotient preserved by the group. -/
def RationalSectionOrbitContinuityStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (d : RationalData K P)
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : G →* locusStabilizer d),
    (∀ a : P, Continuous (fun g : G => (ρ g : Aut P).hom.toAlgHom a)) →
      ∀ b : d.algebra,
        Continuous (fun g : G => (stabilizerSectionAction d (ρ g)).hom.toAlgHom b)

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
