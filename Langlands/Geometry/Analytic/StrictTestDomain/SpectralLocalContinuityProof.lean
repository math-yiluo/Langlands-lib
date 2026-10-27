import Langlands.Geometry.Analytic.StrictTestDomain.SpectralLocalContinuityStatement

/-! # Local spectral continuity for actual rational quotient actions -/

universe u v

set_option maxHeartbeats 50000

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory Filter
open scoped Topology

attribute [local instance] rationalSpectralTopology

section SpectralContinuity

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedStrictAffinoidAlgebra K}
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

omit [IsTopologicalGroup H] in
/-- Uniform spectral displacement and fixed-section evaluation give joint
continuity, without norm continuity of the section orbits. -/
private theorem joint_spectral_evaluation
    (hσ : ∀ (b : A) (g₀ : H) (ε : ℝ), 0 < ε →
      ∀ᶠ g in 𝓝 g₀,
        BanachSpectrum.SpectralBound
          ((σ g).hom.toAlgHom b - (σ g₀).hom.toAlgHom b) ε)
    (b : A) :
    Continuous (fun p : H × BanachSpectrum A => p.2 ((σ p.1).hom.toAlgHom b)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, x₀⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hg := (continuous_fst.tendsto (g₀, x₀))
    (hσ b g₀ (ε / 2) (half_pos hε))
  have hx := Metric.tendsto_nhds.mp
    (((BanachSpectrum.evaluation ((σ g₀).hom.toAlgHom b)).continuous.comp
      continuous_snd).tendsto (g₀, x₀)) (ε / 2) (half_pos hε)
  filter_upwards [hg, hx] with p hp hpx
  change dist (p.2 ((σ g₀).hom.toAlgHom b)) (x₀ ((σ g₀).hom.toAlgHom b)) <
    ε / 2 at hpx
  have hd : dist (p.2 ((σ p.1).hom.toAlgHom b))
      (p.2 ((σ g₀).hom.toAlgHom b)) ≤ ε / 2 := by
    rw [Real.dist_eq]
    exact (abs_sub_map_le_sub p.2.toMulRingSeminorm _ _).trans (hp p.2)
  calc
    dist (p.2 ((σ p.1).hom.toAlgHom b)) (x₀ ((σ g₀).hom.toAlgHom b)) ≤
      dist (p.2 ((σ p.1).hom.toAlgHom b)) (p.2 ((σ g₀).hom.toAlgHom b)) +
      dist (p.2 ((σ g₀).hom.toAlgHom b)) (x₀ ((σ g₀).hom.toAlgHom b)) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hd hpx
    _ = ε := add_halves ε

/-- Inversion converts forward joint evaluations into the existing
inverse-pullback action, with the pointwise spectrum topology. -/
private theorem joint_spectral_action
    (hσ : ∀ b : A,
      Continuous (fun p : H × BanachSpectrum A => p.2 ((σ p.1).hom.toAlgHom b))) :
    Continuous (fun p : H × BanachSpectrum A => (σ p.1) • p.2) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  have h := (hσ b).comp (continuous_fst.inv.prodMk continuous_snd)
  apply h.congr
  intro p
  change p.2 ((σ (p.1⁻¹)).hom.toAlgHom b) = p.2 ((σ p.1).inv.toAlgHom b)
  rw [map_inv]
  rfl

end SpectralContinuity

namespace RationalSpectralAction

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P) (d : RationalData K P)

/-- A positive single-section test gives uniform spectral displacement at one. -/
theorem eventually_spectralBound_one (b : d.algebra) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ g in 𝓝 (1 : ρ.locusOpenSubgroup d),
      BanachSpectrum.SpectralBound ((ρ.sectionAction d g).hom.toAlgHom b - b) ε := by
  have hc : Continuous (fun g : ρ.locusOpenSubgroup d =>
      ρ.toMonoidHom (g : G)) :=
    ρ.continuous_toMonoidHom.comp continuous_subtype_val
  have ho := (isOpen_rationalSpectralSubgroup P d b ε hε).preimage hc
  have h₁ : ρ.toMonoidHom ((1 : ρ.locusOpenSubgroup d) : G) ∈
      rationalSpectralSubgroup d b ε hε.le := by
    simpa only [OneMemClass.coe_one, map_one] using
      (rationalSpectralSubgroup d b ε hε.le).one_mem
  filter_upwards [ho.mem_nhds h₁] with g hg
  obtain ⟨hg', hb⟩ := (mem_rationalSpectralSubgroup d b ε hε.le
    (ρ.toMonoidHom (g : G))).mp hg
  exact hb

end RationalSpectralAction

/-- The exact published local spectral continuity statement. -/
theorem rationalSpectralLocalContinuity :
    RationalSpectralLocalContinuityStatement.{u, v} := by
  intro K _ _ _ P G _ _ _ ρ d
  let : IsTopologicalGroup (ρ.locusOpenSubgroup d) :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup
      (SubgroupClass.subtype (ρ.locusOpenSubgroup d))
  have hbound := spectral_displacement_all (ρ.sectionAction d)
    (ρ.eventually_spectralBound_one d)
  have heval := joint_spectral_evaluation (ρ.sectionAction d) hbound
  exact ⟨hbound, heval, joint_spectral_action (ρ.sectionAction d) heval⟩

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
