import Langlands.Geometry.Analytic.StrictTestDomain.RationalStabilizerAction
import Langlands.Geometry.Analytic.Spectrum.Nonarchimedean

/-! # Spectral small-displacement subgroups on actual rational quotients -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace BanachSpectrum

variable {A B : Type*} [NormedCommRing A] [NormedCommRing B]

/-- A uniform spectral bound, expressed without choosing a maximum or requiring
the spectrum to be nonempty. -/
def SpectralBound (a : A) (r : ℝ) : Prop :=
  ∀ x : BanachSpectrum A, x a ≤ r

theorem SpectralBound.mono {a : A} {r s : ℝ}
    (h : SpectralBound a r) (hrs : r ≤ s) : SpectralBound a s :=
  fun x => (h x).trans hrs

theorem spectralBound_zero {r : ℝ} (hr : 0 ≤ r) :
    SpectralBound (0 : A) r := by
  intro x
  simpa only [map_zero] using hr

theorem SpectralBound.neg {a : A} {r : ℝ} (h : SpectralBound a r) :
    SpectralBound (-a) r := by
  intro x
  simpa only [map_neg_eq_map] using h x

/-- Bounded homomorphisms preserve spectral bounds, without a norm-isometry
assumption: every target point pulls back to a source point. -/
theorem SpectralBound.map {a : A} {r : ℝ} (h : SpectralBound a r)
    (f : BoundedRingHom A B) : SpectralBound (f a) r :=
  fun x => h (comap f x)

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]

include K in
theorem SpectralBound.add {a b : A} {r : ℝ}
    (ha : SpectralBound a r) (hb : SpectralBound b r) :
    SpectralBound (a + b) r :=
  fun x => (x.isNonarchimedean (K := K) a b).trans (max_le (ha x) (hb x))

end BanachSpectrum

namespace StrictTestDomain.RationalAutomorphism

open CategoryTheory BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Automorphisms whose displacement of one element has the given spectral
bound. Multiplication applies the right automorphism first. -/
def spectralDisplacementSubgroup (b : P) (r : ℝ) (hr : 0 ≤ r) :
    Subgroup (Aut P) where
  carrier := {g | SpectralBound (g.hom.toAlgHom b - b) r}
  one_mem' := by
    change SpectralBound (b - b) r
    simpa only [sub_self] using (spectralBound_zero (A := P) hr)
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
      congrArg (fun f : BoundedAlgHom K P P => f b) g.hom_inv_id
    convert hmap using 1
    change g.inv.toAlgHom b - b = g.inv.toAlgHom (-(g.hom.toAlgHom b - b))
    rw [map_neg, map_sub, hinv]
    abel

@[simp] theorem mem_spectralDisplacementSubgroup (b : P) (r : ℝ) (hr : 0 ≤ r)
    (g : Aut P) :
    g ∈ spectralDisplacementSubgroup b r hr ↔
      ∀ x : BanachSpectrum P, x (g.hom.toAlgHom b - b) ≤ r := Iff.rfl

theorem spectralDisplacementSubgroup_mono (b : P) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    spectralDisplacementSubgroup b r hr ≤ spectralDisplacementSubgroup b s hs :=
  fun _ hg => SpectralBound.mono hg hrs

@[simp] theorem spectralDisplacementSubgroup_zero (r : ℝ) (hr : 0 ≤ r) :
    spectralDisplacementSubgroup (0 : P) r hr = ⊤ := by
  ext g
  simp only [mem_spectralDisplacementSubgroup, Subgroup.mem_top, iff_true]
  intro x
  simpa only [map_zero, sub_zero] using hr

variable [CompleteSpace K]

/-- Small displacement on the actual fixed rational quotient, as a subgroup of
its setwise locus stabilizer. -/
def stabilizerSpectralSubgroup (d : RationalData K P) (b : d.algebra)
    (r : ℝ) (hr : 0 ≤ r) : Subgroup (locusStabilizer d) :=
  (spectralDisplacementSubgroup b r hr).comap (stabilizerSectionAction d)

@[simp] theorem mem_stabilizerSpectralSubgroup (d : RationalData K P)
    (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) (g : locusStabilizer d) :
    g ∈ stabilizerSpectralSubgroup d b r hr ↔
      ∀ x : BanachSpectrum d.algebra,
        x ((stabilizerSectionAction d g).hom.toAlgHom b - b) ≤ r := Iff.rfl

/-- The same rational test inside the ambient automorphism group. Membership
includes preservation of the actual rational locus. -/
def rationalSpectralSubgroup (d : RationalData K P) (b : d.algebra)
    (r : ℝ) (hr : 0 ≤ r) : Subgroup (Aut P) :=
  (stabilizerSpectralSubgroup d b r hr).map (locusStabilizer d).subtype

theorem mem_rationalSpectralSubgroup (d : RationalData K P)
    (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) (g : Aut P) :
    g ∈ rationalSpectralSubgroup d b r hr ↔
      ∃ hg : g ∈ locusStabilizer d,
        ∀ x : BanachSpectrum d.algebra,
          x ((stabilizerSectionAction d ⟨g, hg⟩).hom.toAlgHom b - b) ≤ r := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.property, hh⟩
  · rintro ⟨hg, hbound⟩
    exact ⟨⟨g, hg⟩, hbound, rfl⟩

theorem rationalSpectralSubgroup_le_locusStabilizer (d : RationalData K P)
    (b : d.algebra) (r : ℝ) (hr : 0 ≤ r) :
    rationalSpectralSubgroup d b r hr ≤ locusStabilizer d := by
  rintro g ⟨h, _, rfl⟩
  exact h.property

theorem rationalSpectralSubgroup_mono (d : RationalData K P) (b : d.algebra)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    rationalSpectralSubgroup d b r hr ≤ rationalSpectralSubgroup d b s hs := by
  intro g hg
  obtain ⟨hmem, hbound⟩ := (mem_rationalSpectralSubgroup d b r hr g).mp hg
  exact (mem_rationalSpectralSubgroup d b s hs g).mpr
    ⟨hmem, fun x => (hbound x).trans hrs⟩

@[simp] theorem rationalSpectralSubgroup_zero (d : RationalData K P)
    (r : ℝ) (hr : 0 ≤ r) :
    rationalSpectralSubgroup d 0 r hr = locusStabilizer d := by
  ext g
  rw [mem_rationalSpectralSubgroup]
  constructor
  · rintro ⟨hg, _⟩
    exact hg
  · intro hg
    refine ⟨hg, ?_⟩
    intro x
    simpa only [map_zero, sub_zero] using hr

/-- One rational-domain test, using an actual quotient section and a positive
spectral tolerance. -/
structure RationalSpectralTest (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (P : PresentedStrictAffinoidAlgebra K) where
  domain : RationalData K P
  element : domain.algebra
  radius : ℝ
  radius_pos : 0 < radius

/-- A finite family of local tests imposes all domain and section conditions. -/
def finiteRationalSpectralSubgroup {ι : Type v} [Finite ι]
    (tests : ι → RationalSpectralTest K P) : Subgroup (Aut P) :=
  ⨅ i, rationalSpectralSubgroup (tests i).domain (tests i).element
    (tests i).radius (tests i).radius_pos.le

@[simp] theorem mem_finiteRationalSpectralSubgroup {ι : Type v} [Finite ι]
    (tests : ι → RationalSpectralTest K P) (g : Aut P) :
    g ∈ finiteRationalSpectralSubgroup tests ↔
      ∀ i, ∃ hg : g ∈ locusStabilizer (tests i).domain,
        ∀ x : BanachSpectrum (tests i).domain.algebra,
          x ((stabilizerSectionAction (tests i).domain ⟨g, hg⟩).hom.toAlgHom
            (tests i).element - (tests i).element) ≤ (tests i).radius := by
  simp only [finiteRationalSpectralSubgroup, Subgroup.mem_iInf,
    mem_rationalSpectralSubgroup]

@[simp] theorem finiteRationalSpectralSubgroup_empty {ι : Type v} [IsEmpty ι]
    (tests : ι → RationalSpectralTest K P) :
    finiteRationalSpectralSubgroup tests = ⊤ := by
  simp [finiteRationalSpectralSubgroup]

/-- Concatenating finite local tests intersects the resulting subgroups. -/
theorem finiteRationalSpectralSubgroup_sum {ι κ : Type v} [Finite ι] [Finite κ]
    (s : ι → RationalSpectralTest K P) (t : κ → RationalSpectralTest K P) :
    finiteRationalSpectralSubgroup (Sum.elim s t) =
      finiteRationalSpectralSubgroup s ⊓ finiteRationalSpectralSubgroup t := by
  ext g
  simp [finiteRationalSpectralSubgroup, Subgroup.mem_iInf, Sum.forall]

end StrictTestDomain.RationalAutomorphism

end Langlands.Analytic
