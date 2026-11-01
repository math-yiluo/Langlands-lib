import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAutomorphismTransport
import Langlands.Geometry.Analytic.StrictTestDomain.SpectralDisplacement
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Spectral displacement tests on full represented affinoid domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism

open CategoryTheory BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- Automorphisms whose displacement of one element has the given spectral
bound. Multiplication applies the right automorphism first. -/
def spectralDisplacementSubgroup (b : A) (r : ℝ) (hr : 0 ≤ r) :
    Subgroup (Aut A) where
  carrier := {g | SpectralBound (g.hom.toAlgHom b - b) r}
  one_mem' := by
    change SpectralBound (b - b) r
    simpa only [sub_self] using (spectralBound_zero (A := A) hr)
  mul_mem' := by
    intro g h hg hh
    change SpectralBound (g.hom.toAlgHom (h.hom.toAlgHom b) - b) r
    have hmap := hh.map g.hom.toBoundedRingHom
    have hadd := hmap.add (K := K) hg
    convert hadd using 1
    change g.hom.toAlgHom (h.hom.toAlgHom b) - b =
      g.hom.toAlgHom (h.hom.toAlgHom b - b) + (g.hom.toAlgHom b - b)
    rw [map_sub]
    abel
  inv_mem' := by
    intro g hg
    change SpectralBound (g.inv.toAlgHom b - b) r
    have hmap := hg.neg.map g.inv.toBoundedRingHom
    have hinv : g.inv.toAlgHom (g.hom.toAlgHom b) = b :=
      congrArg (fun f : BoundedAlgHom K A A => f b) g.hom_inv_id
    convert hmap using 1
    change g.inv.toAlgHom b - b = g.inv.toAlgHom (-(g.hom.toAlgHom b - b))
    rw [map_neg, map_sub, hinv]
    abel

@[simp] theorem mem_spectralDisplacementSubgroup (b : A) (r : ℝ) (hr : 0 ≤ r)
    (g : Aut A) :
    g ∈ spectralDisplacementSubgroup b r hr ↔
      ∀ x : BanachSpectrum A, x (g.hom.toAlgHom b - b) ≤ r := Iff.rfl

theorem spectralDisplacementSubgroup_mono (b : A) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    spectralDisplacementSubgroup b r hr ≤ spectralDisplacementSubgroup b s hs :=
  fun _ hg => SpectralBound.mono hg hrs

@[simp] theorem spectralDisplacementSubgroup_zero (r : ℝ) (hr : 0 ≤ r) :
    spectralDisplacementSubgroup (0 : A) r hr = ⊤ := by
  ext g
  simp only [mem_spectralDisplacementSubgroup, Subgroup.mem_top, iff_true]
  intro x
  simpa only [map_zero, sub_zero] using hr

variable [CompleteSpace K]

/-- Small displacement on the actual fixed represented affinoid quotient, as a subgroup of
its setwise locus stabilizer. -/
def stabilizerSpectralSubgroup (d : Domain K A) (b : d.algebra)
    (r : ℝ) (hr : 0 ≤ r) : Subgroup (locusStabilizer d) :=
  (spectralDisplacementSubgroup b r hr).comap (stabilizerSectionAction d)

@[simp] theorem mem_stabilizerSpectralSubgroup (d : Domain K A)
    (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) (g : locusStabilizer d) :
    g ∈ stabilizerSpectralSubgroup d b r hr ↔
      ∀ x : BanachSpectrum d.algebra,
        x ((stabilizerSectionAction d g).hom.toAlgHom b - b) ≤ r := Iff.rfl

/-- The same domain test inside the ambient automorphism group. Membership
includes preservation of the actual domain locus. -/
def domainSpectralSubgroup (d : Domain K A) (b : d.algebra)
    (r : ℝ) (hr : 0 ≤ r) : Subgroup (Aut A) :=
  (stabilizerSpectralSubgroup d b r hr).map (locusStabilizer d).subtype

theorem mem_domainSpectralSubgroup (d : Domain K A)
    (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) (g : Aut A) :
    g ∈ domainSpectralSubgroup d b r hr ↔
      ∃ hg : g ∈ locusStabilizer d,
        ∀ x : BanachSpectrum d.algebra,
          x ((stabilizerSectionAction d ⟨g, hg⟩).hom.toAlgHom b - b) ≤ r := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.property, hh⟩
  · rintro ⟨hg, hbound⟩
    exact ⟨⟨g, hg⟩, hbound, rfl⟩

theorem domainSpectralSubgroup_le_locusStabilizer (d : Domain K A)
    (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) :
    domainSpectralSubgroup d b r hr ≤ locusStabilizer d := by
  rintro g ⟨h, _, rfl⟩
  exact h.property

theorem domainSpectralSubgroup_mono (d : Domain K A) (b : d.algebra)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    domainSpectralSubgroup d b r hr ≤ domainSpectralSubgroup d b s hs := by
  intro g hg
  obtain ⟨hmem, hbound⟩ := (mem_domainSpectralSubgroup d b r hr g).mp hg
  exact (mem_domainSpectralSubgroup d b s hs g).mpr
    ⟨hmem, fun x => (hbound x).trans hrs⟩

@[simp] theorem domainSpectralSubgroup_zero (d : Domain K A)
    (r : ℝ) (hr : 0 ≤ r) :
    domainSpectralSubgroup d 0 r hr = locusStabilizer d := by
  ext g
  rw [mem_domainSpectralSubgroup]
  constructor
  · rintro ⟨hg, _⟩
    exact hg
  · intro hg
    refine ⟨hg, ?_⟩
    intro x
    simpa only [map_zero, sub_zero] using hr

/-- One represented affinoid domain test, using an actual quotient section and a positive
spectral tolerance. -/
structure DomainSpectralTest (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) where
  domain : Domain K A
  element : domain.algebra
  radius : ℝ
  radius_pos : 0 < radius

/-- A finite family of local tests imposes all domain and section conditions. -/
def finiteDomainSpectralSubgroup {ι : Type v} [Finite ι]
    (tests : ι → DomainSpectralTest K A) : Subgroup (Aut A) :=
  ⨅ i, domainSpectralSubgroup (tests i).domain (tests i).element
    (tests i).radius (tests i).radius_pos.le

@[simp] theorem mem_finiteDomainSpectralSubgroup {ι : Type v} [Finite ι]
    (tests : ι → DomainSpectralTest K A) (g : Aut A) :
    g ∈ finiteDomainSpectralSubgroup tests ↔
      ∀ i, ∃ hg : g ∈ locusStabilizer (tests i).domain,
        ∀ x : BanachSpectrum (tests i).domain.algebra,
          x ((stabilizerSectionAction (tests i).domain ⟨g, hg⟩).hom.toAlgHom
            (tests i).element - (tests i).element) ≤ (tests i).radius := by
  simp only [finiteDomainSpectralSubgroup, Subgroup.mem_iInf,
    mem_domainSpectralSubgroup]

@[simp] theorem finiteDomainSpectralSubgroup_empty {ι : Type v} [IsEmpty ι]
    (tests : ι → DomainSpectralTest K A) :
    finiteDomainSpectralSubgroup tests = ⊤ := by
  simp [finiteDomainSpectralSubgroup]

/-- Concatenating finite local tests intersects the resulting subgroups. -/
theorem finiteDomainSpectralSubgroup_sum {ι κ : Type v} [Finite ι] [Finite κ]
    (s : ι → DomainSpectralTest K A) (t : κ → DomainSpectralTest K A) :
    finiteDomainSpectralSubgroup (Sum.elim s t) =
      finiteDomainSpectralSubgroup s ⊓ finiteDomainSpectralSubgroup t := by
  ext g
  simp [finiteDomainSpectralSubgroup, Subgroup.mem_iInf, Sum.forall]

/-- Conjugation preserves the section bound after moving the full domain.
The section element and its quotient norm are unchanged. -/
theorem conjugate_mem_stabilizerSpectralSubgroup_iff
    (U : Domain K A) (g h : Aut A) (b : U.algebra) (r : ℝ) (hr : 0 ≤ r)
    (hh : h ∈ locusStabilizer U)
    (hm : g * h * g⁻¹ ∈ locusStabilizer (movedDomain U g)) :
    (⟨g * h * g⁻¹, hm⟩ : locusStabilizer (movedDomain U g)) ∈
      stabilizerSpectralSubgroup (movedDomain U g) b r hr ↔
    (⟨h, hh⟩ : locusStabilizer U) ∈ stabilizerSpectralSubgroup U b r hr := by
  change SpectralBound (movedSectionMap U g ⟨g * h * g⁻¹, hm⟩ b - b) r ↔
    SpectralBound (stabilizerSectionMap U ⟨h, hh⟩ b - b) r
  rw [stabilizerSectionMap_conjugate U g h hh hm]

/-- Passing the original domain test is equivalent to passing its moved
version after conjugation. -/
theorem conjugate_mem_domainSpectralSubgroup_iff
    (U : Domain K A) (g h : Aut A) (b : U.algebra) (r : ℝ) (hr : 0 ≤ r) :
    g * h * g⁻¹ ∈ domainSpectralSubgroup (movedDomain U g) b r hr ↔
      h ∈ domainSpectralSubgroup U b r hr := by
  constructor
  · intro hmem
    obtain ⟨hm, hb⟩ := (mem_domainSpectralSubgroup (movedDomain U g) b r hr
      (g * h * g⁻¹)).mp hmem
    have hh := (conjugate_mem_locusStabilizer_iff U g h).mp hm
    exact (mem_domainSpectralSubgroup U b r hr h).mpr
      ⟨hh, (conjugate_mem_stabilizerSpectralSubgroup_iff U g h b r hr hh hm).mp hb⟩
  · intro hmem
    obtain ⟨hh, hb⟩ := (mem_domainSpectralSubgroup U b r hr h).mp hmem
    have hm := (conjugate_mem_locusStabilizer_iff U g h).mpr hh
    exact (mem_domainSpectralSubgroup (movedDomain U g) b r hr (g * h * g⁻¹)).mpr
      ⟨hm, (conjugate_mem_stabilizerSpectralSubgroup_iff U g h b r hr hh hm).mpr hb⟩

/-- Move a represented domain test, retaining its actual section element
and its positive tolerance on exactly the same section algebra. -/
def DomainSpectralTest.transport (g : Aut A) (t : DomainSpectralTest K A) :
    DomainSpectralTest K A where
  domain := movedDomain t.domain g
  element := t.element
  radius := t.radius
  radius_pos := t.radius_pos

/-- The transported single test defines exactly the conjugate subgroup. -/
theorem DomainSpectralTest.subgroup_transport (g : Aut A)
    (t : DomainSpectralTest K A) :
    domainSpectralSubgroup (t.transport g).domain (t.transport g).element
      (t.transport g).radius (t.transport g).radius_pos.le =
      (domainSpectralSubgroup t.domain t.element t.radius t.radius_pos.le).map
        (MulAut.conj g).toMonoidHom := by
  ext h
  obtain ⟨h, rfl⟩ := (MulAut.conj g).surjective h
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  exact conjugate_mem_domainSpectralSubgroup_iff t.domain g h t.element t.radius
    t.radius_pos.le

/-- Transport commutes with finite intersections of tests, including the
empty family, with an independent universe for the finite index. -/
theorem finiteDomainSpectralSubgroup_transport {ι : Type v} [Finite ι]
    (g : Aut A) (tests : ι → DomainSpectralTest K A) :
    finiteDomainSpectralSubgroup (fun i => (tests i).transport g) =
      (finiteDomainSpectralSubgroup tests).map (MulAut.conj g).toMonoidHom := by
  ext h
  obtain ⟨h, rfl⟩ := (MulAut.conj g).surjective h
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  simp only [finiteDomainSpectralSubgroup, Subgroup.mem_iInf,
    DomainSpectralTest.transport]
  exact forall_congr' fun i => conjugate_mem_domainSpectralSubgroup_iff
    (tests i).domain g h (tests i).element (tests i).radius (tests i).radius_pos.le

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism
