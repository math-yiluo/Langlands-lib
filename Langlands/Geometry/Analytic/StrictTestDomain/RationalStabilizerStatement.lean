import Langlands.Geometry.Analytic.StrictTestDomain.RationalAutomorphism
import Mathlib.Topology.Algebra.Group.Basic

/-! # Open setwise stabilizers of actual rational loci -/

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory

/-- Norm-continuous algebra-element orbits imply that each actual unit-radius
rational locus has an open setwise stabilizer under the inverse-pullback
spectrum action. -/
def RationalLocusStabilizerOpenStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K]
    (P : PresentedStrictAffinoidAlgebra K)
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : G →* Aut P),
    (∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) →
      ∀ d : RationalData K P,
        IsOpen {g : G |
          (fun x : BanachSpectrum P => (ρ g) • x) '' d.locus = d.locus}

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
