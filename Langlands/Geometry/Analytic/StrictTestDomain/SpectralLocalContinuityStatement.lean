import Langlands.Geometry.Analytic.StrictTestDomain.SpectralAction

/-! # Local spectral continuity targets for rational quotient actions -/

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory
open scoped Topology

/-- Continuity for the rational spectral topology gives uniform spectral
displacement control, jointly continuous section evaluations, and a jointly
continuous inverse-pullback action on each fixed rational quotient spectrum. -/
def RationalSpectralLocalContinuityStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K)
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : RationalSpectralAction G P) (d : RationalData K P),
    (∀ (b : d.algebra) (g₀ : ρ.locusOpenSubgroup d) (ε : ℝ), 0 < ε →
      ∀ᶠ g in 𝓝 g₀,
        BanachSpectrum.SpectralBound
          ((ρ.sectionAction d g).hom.toAlgHom b -
            (ρ.sectionAction d g₀).hom.toAlgHom b) ε) ∧
    (∀ b : d.algebra,
      Continuous (fun p : ρ.locusOpenSubgroup d × BanachSpectrum d.algebra =>
        p.2 ((ρ.sectionAction d p.1).hom.toAlgHom b))) ∧
    Continuous (fun p : ρ.locusOpenSubgroup d × BanachSpectrum d.algebra =>
      (ρ.sectionAction d p.1) • p.2)

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
