import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralAction

/-! # Local spectral continuity targets for represented affinoid domains -/

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism

open scoped Topology

/-- Continuity for the represented-domain spectral topology gives uniform
spectral displacement at every parameter, joint section evaluation continuity,
and joint continuity of inverse pullback on each fixed represented spectrum. -/
def DomainSpectralLocalContinuityStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedAffinoidAlgebra K)
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : DomainSpectralAction G P) (d : Domain K P),
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

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism
