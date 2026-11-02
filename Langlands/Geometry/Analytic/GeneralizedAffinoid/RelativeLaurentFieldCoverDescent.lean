import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentFieldDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentCoverDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange

/-! # Rational-cover descent from the independent Laurent coefficient field -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} {L : Type v} [NormedField K] [IsUltrametricDist K]
  [NormedField L] [IsUltrametricDist L]
  {A : PresentedAffinoidAlgebra K} {B : PresentedAffinoidAlgebra L}

/-- Transport the actual coefficient classes along a bounded ring map, allowing
the displayed coefficient fields to differ. -/
def ringPullback (φ : BoundedRingHom A B) (d : RationalChart K A) :
    RationalChart L B where
  arity := d.arity
  radii := d.radii
  denominator := coefficientRepresentative B (φ (presentationMap K A d.denominator))
  numerators j := coefficientRepresentative B (φ (presentationMap K A (d.numerators j)))
  generates := by
    change Ideal.span (insert
      (presentationMap L B (coefficientRepresentative B (φ (presentationMap K A d.denominator))))
      (Set.range fun j => presentationMap L B
        (coefficientRepresentative B (φ (presentationMap K A (d.numerators j)))))) = ⊤
    simp only [presentationMap_coefficientRepresentative]
    let J : Ideal B := Ideal.span (insert (φ (presentationMap K A d.denominator))
      (Set.range fun j => φ (presentationMap K A (d.numerators j))))
    change J = ⊤
    have hle : Ideal.span (insert (presentationMap K A d.denominator)
        (Set.range fun j => presentationMap K A (d.numerators j))) ≤
          Ideal.comap φ.toRingHom J := by
      apply Ideal.span_le.mpr
      intro a ha
      rcases ha with rfl | ⟨j, rfl⟩
      · change φ (presentationMap K A d.denominator) ∈ J
        exact Ideal.subset_span (Set.mem_insert _ _)
      · change φ (presentationMap K A (d.numerators j)) ∈ J
        exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j))
    have h1 := hle (show (1 : A) ∈ Ideal.span
        (insert (presentationMap K A d.denominator)
          (Set.range fun j => presentationMap K A (d.numerators j))) by
      rw [d.generates]
      trivial)
    exact J.eq_top_iff_one.mpr (by simpa only [Ideal.mem_comap, map_one] using h1)

@[simp] theorem ringPullback_denominator_class
    (φ : BoundedRingHom A B) (d : RationalChart K A) :
    presentationMap L B (ringPullback φ d).denominator =
      φ (presentationMap K A d.denominator) :=
  presentationMap_coefficientRepresentative B _

@[simp] theorem ringPullback_numerator_class
    (φ : BoundedRingHom A B) (d : RationalChart K A) (j : Fin d.arity) :
    presentationMap L B ((ringPullback φ d).numerators j) =
      φ (presentationMap K A (d.numerators j)) :=
  presentationMap_coefficientRepresentative B _

/-- Changing the displayed coefficient field does not change the transported
inequalities: they are exactly the inverse image under the bounded spectrum map. -/
theorem ringPullback_locus (φ : BoundedRingHom A B) (d : RationalChart K A) :
    (ringPullback φ d).locus = (BanachSpectrum.comap φ) ⁻¹' d.locus := by
  ext x
  change (∀ j : Fin d.arity, x (presentationMap L B ((ringPullback φ d).numerators j)) ≤
    d.radii j * x (presentationMap L B (ringPullback φ d).denominator)) ↔
      ∀ j, x (φ (presentationMap K A (d.numerators j))) ≤
        d.radii j * x (φ (presentationMap K A d.denominator))
  simp only [ringPullback_denominator_class, ringPullback_numerator_class]

end PresentedAffinoidAlgebra.RationalChart

namespace RelativeLaurentAnnulus.ScalarExtension

open PresentedAffinoidAlgebra CategoryTheory Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (t : ℝ) [Fact (0 < t)]
  [H : Fact (∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n)]
  {A : PresentedAffinoidAlgebra K}

/-- Re-express a coefficient-field rational chart over the actual K-annulus by
transporting its coefficient classes through the bounded inverse comparison. -/
def annulusChart (d : RationalChart (CompletedGaussLaurent K t) (presentation K A t)) :
    RationalChart K (algebra K A t) :=
  RationalChart.ringPullback (fromPresentation K A t).toBoundedRingHom d

theorem annulusChart_locus
    (d : RationalChart (CompletedGaussLaurent K t) (presentation K A t)) :
    (annulusChart K t d).locus =
      (boundedEquiv K A t).spectrumHomeomorph.symm ⁻¹' d.locus :=
  RationalChart.ringPullback_locus _ d

/-- The inverse ambient spectrum homeomorphism respects the actual domain loci. -/
def annulusToFieldLocus (U : Domain K A) :
    C((liftedDomain K t U).locus, (fieldDomain K t U).locus) := by
  refine ⟨fun x => ⟨(boundedEquiv K A t).spectrumHomeomorph.symm x.val, ?_⟩, ?_⟩
  ·
    change (boundedEquiv K A t).spectrumHomeomorph
      ((boundedEquiv K A t).spectrumHomeomorph.symm x.val) ∈
        (liftedDomain K t U).locus
    simpa only [Homeomorph.apply_symm_apply] using x.property
  · exact ((boundedEquiv K A t).spectrumHomeomorph.symm.continuous.comp
      continuous_subtype_val).subtype_mk _

/-- Actual bounded restrictions are supplied by the full K-domain
representation after the exact chart-locus transport. -/
def annulusChartMap (U : Domain K A)
    (d : RationalChart (CompletedGaussLaurent K t) (presentation K A t))
    (f : d.toDomain ⟶ fieldDomain K t U) :
    (annulusChart K t d).toDomain ⟶ liftedDomain K t U :=
  Domain.inclusionOfSubset _ _ (by
    intro x hx
    change x ∈ (annulusChart K t d).locus at hx
    rw [annulusChart_locus] at hx
    have h := f.subset hx
    change (boundedEquiv K A t).spectrumHomeomorph
      ((boundedEquiv K A t).spectrumHomeomorph.symm x) ∈
        (liftedDomain K t U).locus at h
    simpa only [Homeomorph.apply_symm_apply] using h)

/-- A finite coefficient-field rational cover gives a finite K-rational cover
of the actual lifted domain, with genuine bounded restrictions. -/
def annulusFiniteRationalCover (U : Domain K A)
    (c : Domain.FiniteRationalCover (fieldDomain K t U)) :
    Domain.FiniteRationalCover (liftedDomain K t U) where
  size := c.size
  chart i := annulusChart K t (c.chart i)
  map i := annulusChartMap K t U (c.chart i) (c.map i)
  covers x hx := by
    obtain ⟨i, hi⟩ := c.covers _ (annulusToFieldLocus K t U ⟨x, hx⟩).property
    exact ⟨i, (Set.ext_iff.mp (annulusChart_locus K t (c.chart i)) x).mpr hi⟩

/-- Descend a finite rational cover from the actual independent coefficient-field
domain to the original full affinoid domain. -/
def fieldFiniteRationalCoverDescent (U : Domain K A)
    (c : Domain.FiniteRationalCover (fieldDomain K t U)) :
    Domain.FiniteRationalCover U :=
  finiteRationalCoverDescent K t U (annulusFiniteRationalCover K t U c)

/-- The continuous section from the original domain into its actual
coefficient-field extension. -/
def fieldDomainGaussSection (U : Domain K A) :
    C(U.locus, (fieldDomain K t U).locus) :=
  (annulusToFieldLocus K t U).comp (domainGaussSection K t U)

/-- Transport a finite union of rational neighborhoods to the actual K-annulus. -/
def annulusFiniteRationalNeighborhood (U : Domain K A)
    (x : (liftedDomain K t U).locus)
    (N : Domain.FiniteRationalNeighborhood (fieldDomain K t U)
      (annulusToFieldLocus K t U x)) :
    Domain.FiniteRationalNeighborhood (liftedDomain K t U) x :=
  Domain.FiniteRationalNeighborhood.ofPreimage
    (annulusToFieldLocus K t U) (annulusToFieldLocus K t U).continuous
    (Subtype.val ⁻¹' ⋃ i, (N.chart i).locus) N.mem_nhds N.size
    (fun i => annulusChart K t (N.chart i))
    (fun i => annulusChartMap K t U (N.chart i) (N.map i)) (by
      ext y
      simp only [Set.mem_preimage, Set.mem_iUnion]
      exact exists_congr fun i =>
        (Set.ext_iff.mp (annulusChart_locus K t (N.chart i)) y.val).symm)

/-- Descend finite-union local rational neighborhoods from the actual completed
coefficient field along the continuous Gauss section. -/
def fieldFiniteRationalNeighborhoodDescent (U : Domain K A) (x : U.locus)
    (N : Domain.FiniteRationalNeighborhood (fieldDomain K t U)
      (fieldDomainGaussSection K t U x)) :
    Domain.FiniteRationalNeighborhood U x :=
  finiteRationalNeighborhoodDescent K t U x
    (annulusFiniteRationalNeighborhood K t U (domainGaussSection K t U x) N)

/-- A single coefficient-field rational neighborhood gives a finite-union
neighborhood over the original field. -/
def fieldRationalNeighborhoodDescent (U : Domain K A) (x : U.locus)
    (N : Domain.RationalNeighborhood (fieldDomain K t U)
      (fieldDomainGaussSection K t U x)) :
    Domain.FiniteRationalNeighborhood U x :=
  fieldFiniteRationalNeighborhoodDescent K t U x
    (Domain.FiniteRationalNeighborhood.single N)

end RelativeLaurentAnnulus.ScalarExtension

end Langlands.Analytic
