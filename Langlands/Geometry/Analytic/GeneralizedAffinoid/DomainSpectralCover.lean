import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralTopology
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainComposition

/-! # Detecting spectral displacement on finite represented-domain covers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

namespace Domain

/-- The actual identity structural map is injective on the whole spectrum. -/
theorem whole_spectrumMap_injective :
    Function.Injective (whole K A).spectrumMap := by
  intro x y h
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun z : BanachSpectrum A => z a) h

namespace FiniteCover

variable {V : Domain K A}

/-- A locus cover covers the target quotient spectrum when its structural
spectrum map is injective. No component injectivity is required. -/
theorem spectrum_jointly_surjective (c : FiniteCover V)
    (hV : Function.Injective V.spectrumMap) (x : BanachSpectrum V.algebra) :
    ∃ (i : Fin c.size) (y : BanachSpectrum (c.obj i).algebra),
      (c.map i).spectrumMap y = x := by
  obtain ⟨i, hi⟩ := c.covers (V.spectrumMap x) (V.represents.hasImageIn x)
  obtain ⟨y, hy⟩ := (c.obj i).spectrumToLocus_surjective ⟨V.spectrumMap x, hi⟩
  exact ⟨i, y, hV (((c.map i).spectrumMap_over_base y).trans
    (congrArg (fun z : (c.obj i).locus => (z : BanachSpectrum A)) hy))⟩

/-- Actual bounded restrictions detect every uniform spectral bound.
The radius may be any real number, and the cover may be empty. -/
theorem spectralBound_iff (c : FiniteCover V)
    (hV : Function.Injective V.spectrumMap) (b : V.algebra) (r : ℝ) :
    SpectralBound b r ↔ ∀ i, SpectralBound ((c.map i).restriction b) r := by
  constructor
  · intro hb i
    exact hb.map (c.map i).restriction.toBoundedRingHom
  · intro hb x
    obtain ⟨i, y, rfl⟩ := c.spectrum_jointly_surjective hV x
    exact hb i y

/-- Whole-spectrum targets satisfy the detection criterion unconditionally. -/
theorem spectralBound_whole_iff (c : FiniteCover (whole K A)) (b : A) (r : ℝ) :
    SpectralBound b r ↔ ∀ i, SpectralBound ((c.map i).restriction b) r :=
  c.spectralBound_iff whole_spectrumMap_injective b r

/-- Rational-chart targets satisfy it by the proved original spectrum
homeomorphism, retaining the original quotient section and restrictions. -/
theorem spectralBound_rational_iff (d : RationalChart K A)
    (c : FiniteCover d.toDomain) (b : d.algebra) (r : ℝ) :
    SpectralBound b r ↔ ∀ i, SpectralBound ((c.map i).restriction b) r :=
  c.spectralBound_iff d.spectrumMap_injective b r

end FiniteCover
end Domain

namespace DomainAutomorphism

open scoped Pointwise

/-- Preserving every component of an actual cover preserves its target locus. -/
theorem mem_locusStabilizer_of_cover {V : Domain K A} (c : Domain.FiniteCover V)
    (g : Aut A) (hg : ∀ i, g ∈ locusStabilizer (c.obj i)) :
    g ∈ locusStabilizer V := by
  apply (mem_locusStabilizer V g).mpr
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := c.covers y hy
    exact (c.map i).subset (smul_mem_locus (c.obj i) ⟨g, hg i⟩ hi)
  · intro hx
    obtain ⟨i, hi⟩ := c.covers x hx
    refine ⟨g⁻¹ • x, (c.map i).subset
      (smul_mem_locus (c.obj i) ⟨g⁻¹, (locusStabilizer (c.obj i)).inv_mem (hg i)⟩ hi),
      ?_⟩
    simp

/-- The genuine bounded restriction/action square also commutes with section
displacement, including arbitrary quotient sections. -/
theorem restriction_sectionDisplacement {U V : Domain K A} (f : U ⟶ V)
    (g : Aut A) (hU : g ∈ locusStabilizer U) (hV : g ∈ locusStabilizer V)
    (b : V.algebra) :
    f.restriction ((stabilizerSectionAction V ⟨g, hV⟩).hom.toAlgHom b - b) =
      (stabilizerSectionAction U ⟨g, hU⟩).hom.toAlgHom (f.restriction b) -
        f.restriction b := by
  change f.restriction (stabilizerSectionMap V ⟨g, hV⟩ b - b) =
    stabilizerSectionMap U ⟨g, hU⟩ (f.restriction b) - f.restriction b
  rw [map_sub]
  exact congrArg (fun φ : BoundedAlgHom K V.algebra U.algebra =>
    φ b - f.restriction b) (stabilizerSectionMap_restriction f g hU hV).symm

/-- On component-preserving automorphisms the restricted section tests
detect exactly the target section test. The additional stabilizers remain
visible as an intersection. -/
theorem domainSpectralSubgroup_cover {V : Domain K A} (c : Domain.FiniteCover V)
    (hV : Function.Injective V.spectrumMap) (b : V.algebra) (r : ℝ) (hr : 0 ≤ r) :
    (⨅ i, domainSpectralSubgroup (c.obj i) ((c.map i).restriction b) r hr) =
      domainSpectralSubgroup V b r hr ⊓ ⨅ i, locusStabilizer (c.obj i) := by
  ext g
  simp only [Subgroup.mem_iInf, Subgroup.mem_inf]
  constructor
  · intro hg
    have hcomp : ∀ i, g ∈ locusStabilizer (c.obj i) :=
      fun i => domainSpectralSubgroup_le_locusStabilizer
        (c.obj i) ((c.map i).restriction b) r hr (hg i)
    have htarget := mem_locusStabilizer_of_cover c g hcomp
    refine ⟨(mem_domainSpectralSubgroup V b r hr g).mpr ⟨htarget, ?_⟩, hcomp⟩
    apply (c.spectralBound_iff hV _ r).mpr
    intro i
    obtain ⟨hi, hb⟩ := (mem_domainSpectralSubgroup (c.obj i)
      ((c.map i).restriction b) r hr g).mp (hg i)
    rw [restriction_sectionDisplacement (c.map i) g hi htarget b]
    exact hb
  · rintro ⟨hg, hcomp⟩ i
    obtain ⟨htarget, hb⟩ := (mem_domainSpectralSubgroup V b r hr g).mp hg
    refine (mem_domainSpectralSubgroup (c.obj i)
      ((c.map i).restriction b) r hr g).mpr ⟨hcomp i, ?_⟩
    have hbound := SpectralBound.map hb (c.map i).restriction.toBoundedRingHom
    change SpectralBound ((c.map i).restriction
      ((stabilizerSectionAction V ⟨g, htarget⟩).hom.toAlgHom b - b)) r at hbound
    rw [restriction_sectionDisplacement (c.map i) g (hcomp i) htarget b] at hbound
    exact hbound

/-- The whole-spectrum case has no extra injectivity assumption. -/
theorem domainSpectralSubgroup_cover_whole (c : Domain.FiniteCover (Domain.whole K A))
    (b : A) (r : ℝ) (hr : 0 ≤ r) :
    (⨅ i, domainSpectralSubgroup (c.obj i) ((c.map i).restriction b) r hr) =
      domainSpectralSubgroup (Domain.whole K A) b r hr ⊓
        ⨅ i, locusStabilizer (c.obj i) :=
  domainSpectralSubgroup_cover c Domain.whole_spectrumMap_injective b r hr

/-- The rational-chart case uses the actual quotient-spectrum homeomorphism. -/
theorem domainSpectralSubgroup_cover_rational (d : RationalChart K A)
    (c : Domain.FiniteCover d.toDomain) (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) :
    (⨅ i, domainSpectralSubgroup (c.obj i) ((c.map i).restriction b) r hr) =
      domainSpectralSubgroup d.toDomain b r hr ⊓ ⨅ i, locusStabilizer (c.obj i) :=
  domainSpectralSubgroup_cover c d.spectrumMap_injective b r hr

/-- Restrict a test to one cover member using the original bounded map and
the same positive radius. -/
def DomainSpectralTest.restrictToCover (t : DomainSpectralTest K A)
    (c : Domain.FiniteCover t.domain) (i : Fin c.size) : DomainSpectralTest K A where
  domain := c.obj i
  element := (c.map i).restriction t.element
  radius := t.radius
  radius_pos := t.radius_pos

/-- Exact finite-test identity after restricting one section test to its cover. -/
theorem DomainSpectralTest.subgroup_restrictToCover (t : DomainSpectralTest K A)
    (c : Domain.FiniteCover t.domain) (h : Function.Injective t.domain.spectrumMap) :
    finiteDomainSpectralSubgroup (t.restrictToCover c) =
      domainSpectralSubgroup t.domain t.element t.radius t.radius_pos.le ⊓
        ⨅ i, locusStabilizer (c.obj i) :=
  domainSpectralSubgroup_cover c h t.element t.radius t.radius_pos.le

/-- The finite restricted tests refine the original target test. -/
theorem DomainSpectralTest.subgroup_restrictToCover_le (t : DomainSpectralTest K A)
    (c : Domain.FiniteCover t.domain) (h : Function.Injective t.domain.spectrumMap) :
    finiteDomainSpectralSubgroup (t.restrictToCover c) ≤
      domainSpectralSubgroup t.domain t.element t.radius t.radius_pos.le := by
  rw [t.subgroup_restrictToCover c h]
  exact inf_le_left

/-- The restricted tests give an actual open subgroup in the existing
represented-domain spectral topology. -/
theorem DomainSpectralTest.isOpen_subgroup_restrictToCover (t : DomainSpectralTest K A)
    (c : Domain.FiniteCover t.domain) :
    @IsOpen (Aut A) (domainSpectralTopology A)
      (finiteDomainSpectralSubgroup (t.restrictToCover c) : Set (Aut A)) :=
  isOpen_finiteDomainSpectralSubgroup A (t.restrictToCover c)

/-- Restrict each member of a family to its chosen actual finite cover.
The index universe is independent of the field universe. -/
def restrictDomainSpectralTestsToCovers {ι : Type v}
    (tests : ι → DomainSpectralTest K A)
    (covers : ∀ i, Domain.FiniteCover (tests i).domain) :
    (Σ i, Fin (covers i).size) → DomainSpectralTest K A :=
  fun ij => (tests ij.1).restrictToCover (covers ij.1) ij.2

/-- Finite-family localization retains exactly the component stabilizer
conditions in addition to the original finite tests. -/
theorem finiteDomainSpectralSubgroup_restrictToCovers {ι : Type v} [Finite ι]
    (tests : ι → DomainSpectralTest K A)
    (covers : ∀ i, Domain.FiniteCover (tests i).domain)
    (h : ∀ i, Function.Injective (tests i).domain.spectrumMap) :
    finiteDomainSpectralSubgroup (restrictDomainSpectralTestsToCovers tests covers) =
      finiteDomainSpectralSubgroup tests ⊓
        ⨅ i, ⨅ j, locusStabilizer ((covers i).obj j) := by
  calc
    _ = ⨅ i, finiteDomainSpectralSubgroup ((tests i).restrictToCover (covers i)) := by
      simp only [finiteDomainSpectralSubgroup, restrictDomainSpectralTestsToCovers,
        iInf_sigma]
    _ = ⨅ i, (domainSpectralSubgroup (tests i).domain (tests i).element
        (tests i).radius (tests i).radius_pos.le ⊓
          ⨅ j, locusStabilizer ((covers i).obj j)) :=
      iInf_congr fun i => (tests i).subgroup_restrictToCover (covers i) (h i)
    _ = _ := iInf_inf_eq

/-- The explicit localized family refines the original finite family. -/
theorem finiteDomainSpectralSubgroup_restrictToCovers_le {ι : Type v} [Finite ι]
    (tests : ι → DomainSpectralTest K A)
    (covers : ∀ i, Domain.FiniteCover (tests i).domain)
    (h : ∀ i, Function.Injective (tests i).domain.spectrumMap) :
    finiteDomainSpectralSubgroup (restrictDomainSpectralTestsToCovers tests covers) ≤
      finiteDomainSpectralSubgroup tests := by
  rw [finiteDomainSpectralSubgroup_restrictToCovers tests covers h]
  exact inf_le_left

/-- Every localized finite family is an identity neighborhood in the
constructed topology; this does not require target injectivity. -/
theorem finiteDomainSpectralSubgroup_restrictToCovers_mem_nhds_one
    {ι : Type v} [Finite ι] (tests : ι → DomainSpectralTest K A)
    (covers : ∀ i, Domain.FiniteCover (tests i).domain) :
    (finiteDomainSpectralSubgroup (restrictDomainSpectralTestsToCovers tests covers) :
      Set (Aut A)) ∈ @nhds (Aut A) (domainSpectralTopology A) 1 :=
  finiteDomainSpectralSubgroup_mem_nhds_one A
    (restrictDomainSpectralTestsToCovers tests covers)

/-- These refining subgroups are open, including for empty families and
empty covers of empty targets. -/
theorem isOpen_finiteDomainSpectralSubgroup_restrictToCovers
    {ι : Type v} [Finite ι] (tests : ι → DomainSpectralTest K A)
    (covers : ∀ i, Domain.FiniteCover (tests i).domain) :
    @IsOpen (Aut A) (domainSpectralTopology A)
      (finiteDomainSpectralSubgroup (restrictDomainSpectralTestsToCovers tests covers) :
        Set (Aut A)) :=
  isOpen_finiteDomainSpectralSubgroup A
    (restrictDomainSpectralTestsToCovers tests covers)

end DomainAutomorphism
end Langlands.Analytic.PresentedAffinoidAlgebra
