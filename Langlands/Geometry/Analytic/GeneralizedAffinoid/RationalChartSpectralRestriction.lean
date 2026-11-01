import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainComposition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralAction

/-! # Continuous spectral restriction to an actual rational domain -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory DomainAutomorphism
open scoped Pointwise Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- The constructed section-action homomorphism with the original rational
quotient algebra as its explicit target. -/
def rationalSectionAction (d : RationalChart K A) :
    locusStabilizer d.toDomain →* Aut d.algebra :=
  stabilizerSectionAction d.toDomain

/-- The original injective rational spectrum map identifies local locus
stabilization with stabilization of its actual ambient extension. -/
theorem mem_locusStabilizer_extendDomain_iff (d : RationalChart K A)
    (U : Domain K d.algebra) (g : locusStabilizer d.toDomain) :
    rationalSectionAction d g ∈ locusStabilizer U ↔
      (g : Aut A) ∈ locusStabilizer (d.extendDomain U) := by
  change (fun x : BanachSpectrum d.algebra =>
      (rationalSectionAction d g) • x) '' U.locus = U.locus ↔
    (fun x : BanachSpectrum A => (g : Aut A) • x) ''
      (d.spectrumMap '' U.locus) = d.spectrumMap '' U.locus
  have himage : d.spectrumMap '' ((fun x : BanachSpectrum d.algebra =>
      (rationalSectionAction d g) • x) '' U.locus) =
      (fun x : BanachSpectrum A => (g : Aut A) • x) ''
        (d.spectrumMap '' U.locus) := by
    simp only [Set.image_image]
    exact Set.image_congr' (stabilizerSectionAction_spectrumMap d.toDomain g)
  constructor
  · intro h
    rw [← himage, h]
  · intro h
    exact d.spectrumMap_injective.image_injective (himage.trans h)

/-- The two constructions give the same full bounded automorphism on the
unchanged section algebra, not merely the same spectrum operator. -/
theorem sectionAction_extendDomain (d : RationalChart K A)
    (U : Domain K d.algebra) (g : locusStabilizer d.toDomain)
    (hU : rationalSectionAction d g ∈ locusStabilizer U)
    (hW : (g : Aut A) ∈ locusStabilizer (d.extendDomain U)) :
    stabilizerSectionAction U ⟨rationalSectionAction d g, hU⟩ =
      stabilizerSectionAction (d.extendDomain U) ⟨g, hW⟩ := by
  apply Iso.ext
  change stabilizerSectionMap U _ = stabilizerSectionMap (d.extendDomain U) _
  apply boundedHom_ext U
  rw [stabilizerSectionMap_comp_baseMap]
  exact (stabilizerSectionMap_restriction (d.extendDomainInclusion U)
    (g : Aut A) hW g.property).symm

/-- Pulling back a local section test is exactly the ambient test on the
extended represented domain, inside the outer rational locus stabilizer. -/
theorem domainSpectralSubgroup_comap_sectionAction (d : RationalChart K A)
    (U : Domain K d.algebra) (b : U.algebra) (r : ℝ) (hr : 0 ≤ r) :
    (domainSpectralSubgroup U b r hr).comap (rationalSectionAction d) =
      (domainSpectralSubgroup (d.extendDomain U) b r hr).comap
        (locusStabilizer d.toDomain).subtype := by
  ext g
  change rationalSectionAction d g ∈ domainSpectralSubgroup U b r hr ↔
    (g : Aut A) ∈ domainSpectralSubgroup (d.extendDomain U) b r hr
  constructor
  · intro hg
    obtain ⟨hU, hb⟩ :=
      (mem_domainSpectralSubgroup U b r hr (d.rationalSectionAction g)).mp hg
    have hW := (d.mem_locusStabilizer_extendDomain_iff U g).mp hU
    apply (mem_domainSpectralSubgroup (d.extendDomain U) b r hr (g : Aut A)).mpr
    refine ⟨hW, ?_⟩
    have heq := congrArg (fun f : Aut U.algebra => f.hom.toAlgHom b - b)
      (d.sectionAction_extendDomain U g hU hW)
    exact fun x => heq ▸ hb x
  · intro hg
    obtain ⟨hW, hb⟩ :=
      (mem_domainSpectralSubgroup (d.extendDomain U) b r hr (g : Aut A)).mp hg
    have hU := (d.mem_locusStabilizer_extendDomain_iff U g).mpr hW
    apply (mem_domainSpectralSubgroup U b r hr (d.rationalSectionAction g)).mpr
    refine ⟨hU, ?_⟩
    have heq := congrArg (fun f : Aut U.algebra => f.hom.toAlgHom b - b)
      (d.sectionAction_extendDomain U g hU hW)
    exact fun x => heq.symm ▸ hb x

/-- Extend a local test by the actual rational domain composition. Its section
algebra, section and positive tolerance are unchanged. -/
def extendSpectralTest (d : RationalChart K A)
    (t : DomainSpectralTest K d.algebra) : DomainSpectralTest K A where
  domain := d.extendDomain t.domain
  element := t.element
  radius := t.radius
  radius_pos := t.radius_pos

/-- The exact pullback identity for a finite family, with an index universe
independent of the field. It also includes the empty family. -/
theorem finiteDomainSpectralSubgroup_comap_sectionAction (d : RationalChart K A)
    {ι : Type v} [Finite ι] (tests : ι → DomainSpectralTest K d.algebra) :
    (finiteDomainSpectralSubgroup tests).comap d.rationalSectionAction =
      (finiteDomainSpectralSubgroup (fun i => d.extendSpectralTest (tests i))).comap
        (locusStabilizer d.toDomain).subtype := by
  simp only [finiteDomainSpectralSubgroup, Subgroup.comap_iInf]
  exact iInf_congr fun i => d.domainSpectralSubgroup_comap_sectionAction
    (tests i).domain (tests i).element (tests i).radius (tests i).radius_pos.le

attribute [local instance] domainSpectralTopology domainSpectralTopology_isTopologicalGroup

/-- The constructed actual section action of a rational locus stabilizer is
continuous for the represented-domain spectral topologies. The stabilizer has
the subspace topology from the ambient automorphism group. -/
theorem continuous_rationalSectionAction (d : RationalChart K A) :
    Continuous d.rationalSectionAction := by
  apply (continuous_domainSpectralTopology_iff d.algebra d.rationalSectionAction).mpr
  intro ι hι tests
  change ((finiteDomainSpectralSubgroup tests).comap d.rationalSectionAction :
    Set (locusStabilizer d.toDomain)) ∈ 𝓝 1
  rw [d.finiteDomainSpectralSubgroup_comap_sectionAction tests]
  exact ((isOpen_finiteDomainSpectralSubgroup A
    (fun i => d.extendSpectralTest (tests i))).preimage
      continuous_subtype_val).mem_nhds (Subgroup.one_mem _)

/-- The continuous action uses the original actual quotient algebra and the
already constructed full bounded automorphisms. -/
def spectralStabilizerAction (d : RationalChart K A) :
    DomainSpectralAction (locusStabilizer d.toDomain) d.algebra where
  toMonoidHom := d.rationalSectionAction
  continuous_toMonoidHom := d.continuous_rationalSectionAction

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- A given continuous ambient action maps its open rational locus stabilizer
continuously into the actual automorphism locus stabilizer. -/
theorem continuous_actionStabilizerHom (d : RationalChart K A)
    (ρ : DomainSpectralAction G A) : Continuous (ρ.stabilizerHom d.toDomain) := by
  exact (ρ.continuous_toMonoidHom.comp continuous_subtype_val).subtype_mk _

/-- Restrict any represented-domain spectral action continuously to the original
rational chart algebra, using its actual open locus stabilizer. -/
def restrictSpectralAction (d : RationalChart K A) (ρ : DomainSpectralAction G A) :
    DomainSpectralAction (ρ.locusOpenSubgroup d.toDomain) d.algebra :=
  d.spectralStabilizerAction.precomp (ρ.stabilizerHom d.toDomain)
    (d.continuous_actionStabilizerHom ρ)

/-- The local continuous action agrees with the previously constructed section
action on the full bounded automorphisms. -/
@[simp] theorem restrictSpectralAction_toMonoidHom (d : RationalChart K A)
    (ρ : DomainSpectralAction G A) :
    (d.restrictSpectralAction ρ).toMonoidHom = ρ.sectionAction d.toDomain := rfl

/-- Restriction retains the original forward action on base-algebra sections. -/
@[simp] theorem restrictSpectralAction_baseMap (d : RationalChart K A)
    (ρ : DomainSpectralAction G A) (g : ρ.locusOpenSubgroup d.toDomain) (a : A) :
    ((d.restrictSpectralAction ρ).toMonoidHom g).hom.toAlgHom (d.baseMap a) =
      d.baseMap ((ρ.toMonoidHom g).hom.toAlgHom a) :=
  ρ.sectionAction_baseMap d.toDomain g a

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
