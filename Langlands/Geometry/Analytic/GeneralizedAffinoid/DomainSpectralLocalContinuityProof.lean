import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralLocalContinuityStatement
import Langlands.Geometry.Analytic.Spectrum.SpectralJointContinuityProof

/-! # Local spectral continuity for full represented affinoid domains

The displacement proof adapts Worker 730's strict local continuity proof.
Joint continuity uses the published general spectral pullback theorem.
-/

universe u v

set_option maxHeartbeats 50000

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism

open CategoryTheory Filter
open scoped Topology

attribute [local instance] domainSpectralTopology

section SpectralDisplacement

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (σ : H →* Aut A)

/-- Translate an identity displacement bound using only the bounded section
automorphisms, before specializing to an actual rational quotient. -/
private theorem spectral_displacement_all
    (hσ : ∀ (b : A) (ε : ℝ), 0 < ε →
      ∀ᶠ g in 𝓝 (1 : H),
        BanachSpectrum.SpectralBound ((σ g).hom.toAlgHom b - b) ε)
    (b : A) (g₀ : H) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ g in 𝓝 g₀,
      BanachSpectrum.SpectralBound
        ((σ g).hom.toAlgHom b - (σ g₀).hom.toAlgHom b) ε := by
  have ht : Tendsto (fun g : H => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa only [inv_mul_cancel] using (continuous_const_mul g₀⁻¹).tendsto g₀
  filter_upwards [ht (hσ b ε hε)] with g hg
  have hm := hg.map (σ g₀).hom.toBoundedRingHom
  have heq : (σ g₀).hom.toAlgHom ((σ (g₀⁻¹ * g)).hom.toAlgHom b) =
      (σ g).hom.toAlgHom b := by
    change ((σ g₀) * (σ (g₀⁻¹ * g))).hom.toAlgHom b = _
    rw [← map_mul, mul_inv_cancel_left]
  change BanachSpectrum.SpectralBound
    ((σ g₀).hom.toAlgHom ((σ (g₀⁻¹ * g)).hom.toAlgHom b - b)) ε at hm
  rw [map_sub, heq] at hm
  exact hm

end SpectralDisplacement

namespace DomainSpectralAction

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P) (d : Domain K P)

/-- A positive single-section test gives uniform spectral displacement at one. -/
theorem eventually_spectralBound_one (b : d.algebra) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ g in 𝓝 (1 : ρ.locusOpenSubgroup d),
      BanachSpectrum.SpectralBound ((ρ.sectionAction d g).hom.toAlgHom b - b) ε := by
  have hc : Continuous (fun g : ρ.locusOpenSubgroup d =>
      ρ.toMonoidHom (g : G)) :=
    ρ.continuous_toMonoidHom.comp continuous_subtype_val
  have ho := (isOpen_domainSpectralSubgroup P d b ε hε).preimage hc
  have h₁ : ρ.toMonoidHom ((1 : ρ.locusOpenSubgroup d) : G) ∈
      domainSpectralSubgroup d b ε hε.le := by
    simpa only [OneMemClass.coe_one, map_one] using
      (domainSpectralSubgroup d b ε hε.le).one_mem
  filter_upwards [ho.mem_nhds h₁] with g hg
  obtain ⟨hg', hb⟩ := (mem_domainSpectralSubgroup d b ε hε.le
    (ρ.toMonoidHom (g : G))).mp hg
  exact hb

end DomainSpectralAction

/-- The represented-domain spectral topology gives the exact local uniform
displacement, forward evaluation and inverse-pullback continuity conclusions. -/
theorem domainSpectralLocalContinuity :
    DomainSpectralLocalContinuityStatement.{u, v} := by
  intro K _ _ _ P G _ _ _ ρ d
  let : IsTopologicalGroup (ρ.locusOpenSubgroup d) :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup
      (SubgroupClass.subtype (ρ.locusOpenSubgroup d))
  have hbound := spectral_displacement_all (ρ.sectionAction d)
    (ρ.eventually_spectralBound_one d)
  have hcomap := BanachSpectrum.spectralParametricPullbackContinuity
    d.algebra d.algebra (ρ.locusOpenSubgroup d)
    (fun g => (ρ.sectionAction d g).hom.toBoundedRingHom) hbound
  have heval : ∀ b : d.algebra,
      Continuous (fun p : ρ.locusOpenSubgroup d × BanachSpectrum d.algebra =>
        p.2 ((ρ.sectionAction d p.1).hom.toAlgHom b)) :=
    fun b => (BanachSpectrum.evaluation b).continuous.comp hcomap
  refine ⟨hbound, heval, ?_⟩
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  have h := (heval b).comp (continuous_fst.inv.prodMk continuous_snd)
  apply h.congr
  intro p
  change p.2 ((ρ.sectionAction d (p.1⁻¹)).hom.toAlgHom b) =
    p.2 ((ρ.sectionAction d p.1).inv.toAlgHom b)
  rw [map_inv]
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism
