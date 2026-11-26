import Langlands.Geometry.Analytic.AffinoidFieldCharacters
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueProof

/-! # Rational loci in analytic atlases and their charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

namespace BanachSpectrum

/-- Points of the affinoid spectrum represented by bounded characters into the ground
field. The subtype has the topology induced from the spectrum. -/
def rationalLocus (B : PresentedAffinoidAlgebra K) : Set (BanachSpectrum B) :=
  {s | ∃ f : BoundedAlgHom K B K, ∀ b, ‖f b‖ = s b}

variable {K} {B : PresentedAffinoidAlgebra K}

/-- The character of a rational spectrum point. Its values are determined by its
seminorm and the scalar action. -/
def rationalCharacter (s : rationalLocus K B) : BoundedAlgHom K B K :=
  s.property.choose

theorem norm_rationalCharacter (s : rationalLocus K B) (b : B) :
    ‖rationalCharacter s b‖ = s.val b :=
  s.property.choose_spec b

/-- Two characters into the ground field with the same seminorm are equal. -/
theorem rationalCharacter_unique (s : rationalLocus K B) (f : BoundedAlgHom K B K)
    (h : ∀ b, ‖f b‖ = s.val b) : f = rationalCharacter s := by
  apply BoundedAlgHom.ext
  intro b
  let c := b - algebraMap K B (rationalCharacter s b)
  have hc : ‖f c‖ = ‖rationalCharacter s c‖ :=
    (h c).trans (norm_rationalCharacter s c).symm
  change ‖f.toAlgHom c‖ = ‖(rationalCharacter s).toAlgHom c‖ at hc
  simp only [c, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self,
    norm_zero, norm_eq_zero, sub_eq_zero] at hc
  exact hc

/-- On the rational locus the value of any affinoid function varies continuously
in the ground field topology. -/
theorem continuous_rationalCharacter_apply (b : B) :
    Continuous (fun s : rationalLocus K B => rationalCharacter s b) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply Metric.continuousAt_iff'.2
  intro ε hε
  let c := b - algebraMap K B (rationalCharacter s b)
  have hd (t : rationalLocus K B) :
      dist (rationalCharacter t b) (rationalCharacter s b) = t.val c := by
    rw [← norm_rationalCharacter t c, dist_eq_norm]
    simp only [c, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply]
  have hopen : IsOpen {t : rationalLocus K B | t.val c < ε} :=
    isOpen_lt ((evaluation c).continuous.comp continuous_subtype_val) continuous_const
  have hs : s ∈ {t : rationalLocus K B | t.val c < ε} := by
    change s.val c < ε
    rwa [← hd s, dist_self]
  filter_upwards [hopen.mem_nhds hs] with t ht
  rw [hd]
  exact ht

end BanachSpectrum

namespace AffinoidAtlasPresentation

variable [CompleteSpace K]

/-- The underlying points of full ground-field-valued points, with the induced
topology on this subset of the analytic space. -/
def rationalLocus (A : AffinoidAtlasPresentation.{u, v, w} K) : Set A.space :=
  range (FieldPoint.point : FieldPoint K A → A.space)

variable {K}

/-- Rationality at an atlas point is detected on any chart containing it. -/
theorem chart_mem_rationalLocus_iff (A : AffinoidAtlasPresentation.{u, v, w} K)
    (i : A.atlas.Index) (s : BanachSpectrum (A.atlas.algebra i)) :
    A.atlas.chart i s ∈ A.rationalLocus K ↔
      s ∈ BanachSpectrum.rationalLocus K (A.atlas.algebra i) := by
  constructor
  · rintro ⟨p, hp⟩
    have hi : p.point ∈ range (A.atlas.chart i) := ⟨s, hp.symm⟩
    obtain ⟨t, ht, hn⟩ := p.isChartPoint i hi
    have hts : t = s := (A.atlas.isEmbedding_chart i).injective (ht.trans hp)
    exact ⟨p.boundedEval i hi, fun b => (hn b).trans (congrArg (fun t => t b) hts)⟩
  · rintro ⟨f, hf⟩
    obtain ⟨p, hp, -⟩ := FieldPoint.existsUnique_of_chartCharacter
      PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity (A.atlas.chart i s) i
        f.toAlgHom ⟨s, rfl, hf⟩
    exact ⟨p, hp.1⟩

end AffinoidAtlasPresentation

end Langlands.Analytic
