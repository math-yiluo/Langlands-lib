import Langlands.Geometry.Analytic.StrictTestDomain.RationalAutomorphism
import Mathlib.Topology.Algebra.Group.Basic

/-! # Joint continuity target for actual strict-affinoid spectrum actions -/

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory

/-- Pointwise norm-continuity of a representation by bounded algebra
automorphisms gives joint continuity of the existing inverse-pullback action
on the actual bounded spectrum. -/
def PointwiseContinuousSpectrumActionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K]
    (P : PresentedStrictAffinoidAlgebra K)
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : G →* Aut P),
    (∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) →
      Continuous (fun p : G × BanachSpectrum P => (ρ p.1) • p.2)

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
