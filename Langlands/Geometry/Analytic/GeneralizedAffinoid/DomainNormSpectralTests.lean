import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormSectionContinuity
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalCoverProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectrumProof

/-! # Spectral tests on full represented domains from norm-continuous orbits -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism

open CategoryTheory Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

/-- A full represented domain is the union of the loci of the rational
charts of a finite rational covering. -/
theorem locus_eq_iUnion_of_cover (U : Domain K A) {n : ℕ} (D : Fin n → RationalChart K A)
    (ι : ∀ k, (D k).toDomain ⟶ U) (hcov : ∀ x ∈ U.locus, ∃ k, x ∈ (D k).locus) :
    U.locus = ⋃ k, (D k).locus := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := hcov x hx
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  · intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact (ι k).subset hk

include hρ in
/-- Norm-continuous base orbits make every single spectral test on an
arbitrary full represented domain an identity neighborhood. The proof covers
the domain by finitely many rational charts and uses that the structural
spectrum map of the domain is injective. -/
theorem domainSpectralSubgroup_mem_nhds_of_normContinuous (U : Domain K A)
    (b : U.algebra) (r : ℝ) (hr : 0 < r) :
    ρ ⁻¹' (domainSpectralSubgroup U b r hr.le : Set (Aut A)) ∈ 𝓝 (1 : G) := by
  obtain ⟨n, D, ι, hcov⟩ := Domain.finiteRationalCover K A U
  have hk : ∀ k, ρ ⁻¹' (domainSpectralSubgroup (D k).toDomain ((ι k).restriction b) r
      hr.le : Set (Aut A)) ∈ 𝓝 (1 : G) :=
    fun k => RationalChart.normDomainSpectralSubgroup_mem_nhds ρ hρ (D k) _ r hr
  filter_upwards [Filter.iInter_mem.mpr hk] with g hg
  simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hg
  have hmem := fun k => (mem_domainSpectralSubgroup _ _ r hr.le (ρ g)).mp (hg k)
  choose hstab hbound using hmem
  have hlocus := locus_eq_iUnion_of_cover U D ι hcov
  have hU : ρ g ∈ locusStabilizer U := by
    rw [mem_locusStabilizer, hlocus, Set.image_iUnion]
    exact Set.iUnion_congr fun k => (mem_locusStabilizer _ _).mp (hstab k)
  refine (mem_domainSpectralSubgroup U b r hr.le (ρ g)).mpr ⟨hU, fun x => ?_⟩
  obtain ⟨k, hxk⟩ := hcov (U.spectrumMap x) (U.represents.hasImageIn x)
  have hxk' : U.spectrumMap x ∈ Set.range (D k).toDomain.spectrumMap := by
    change U.spectrumMap x ∈ Set.range (BanachSpectrum.comap
      (D k).toDomain.baseMap.toBoundedRingHom)
    rw [(D k).toDomain.represents.2.1]
    exact hxk
  obtain ⟨x', hx'⟩ := hxk'
  have hx : (ι k).spectrumMap x' = x := by
    apply (Domain.spectrumEmbedding K A U).injective
    rw [Domain.Inclusion.spectrumMap_over_base]
    exact hx'
  subst hx
  have hres := stabilizerSectionMap_restriction (ι k) (ρ g) (hstab k) hU
  have key : (ι k).restriction
      ((stabilizerSectionAction U ⟨ρ g, hU⟩).hom.toAlgHom b - b) =
      (stabilizerSectionAction (D k).toDomain ⟨ρ g, hstab k⟩).hom.toAlgHom
        ((ι k).restriction b) - (ι k).restriction b := by
    rw [map_sub]
    congr 1
    exact (congrArg (fun φ : BoundedAlgHom K U.algebra (D k).toDomain.algebra => φ b)
      hres).symm
  have hb := hbound k x'
  change x' ((ι k).restriction
    ((stabilizerSectionAction U ⟨ρ g, hU⟩).hom.toAlgHom b - b)) ≤ r
  rw [key]
  exact hb

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism
