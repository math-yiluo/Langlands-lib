import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GaussLaurentRationalPullback
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFiniteRationalNeighborhoods

/-! # Finite rational-cover descent along the actual Laurent Gauss section -/

noncomputable section

universe u v

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra CategoryTheory Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (t : ℝ) [Fact (0 < t)] {A : PresentedAffinoidAlgebra K}

/-- Flatten the finite rational pullbacks of a finite family of annulus charts. -/
theorem exists_finite_family_rational_pullback {I : Type v} [Fintype I]
    (d : I → RationalChart K (algebra K A t)) :
    ∃ (m : ℕ) (D : Fin m → RationalChart K A), ∀ x : BanachSpectrum A,
      (∃ i, sectionPoint K A t x ∈ (d i).locus) ↔
        ∃ j, x ∈ (D j).locus := by
  classical
  let J := (i : I) × Fin (rationalPullbackCharts K t (d i)).1
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J,
    fun j => (rationalPullbackCharts K t (d (e j).1)).2 (e j).2, fun x => ?_⟩
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := (mem_rationalPullbackCharts K t (d i) x).mp hi
    refine ⟨e.symm ⟨i, j⟩, ?_⟩
    dsimp only
    rw [e.apply_symm_apply]
    exact hj
  · rintro ⟨j, hj⟩
    exact ⟨(e j).1, (mem_rationalPullbackCharts K t _ x).mpr ⟨(e j).2, hj⟩⟩

/-- A chosen finite family for the inverse image of a finite union of annulus
rational loci. The index type may inhabit an independent universe. -/
def rationalFamilyPullbackCharts {I : Type v} [Fintype I]
    (d : I → RationalChart K (algebra K A t)) :
    Σ m : ℕ, Fin m → RationalChart K A :=
  ⟨(exists_finite_family_rational_pullback K t d).choose,
    (exists_finite_family_rational_pullback K t d).choose_spec.choose⟩

theorem mem_rationalFamilyPullbackCharts {I : Type v} [Fintype I]
    (d : I → RationalChart K (algebra K A t)) (x : BanachSpectrum A) :
    (∃ i, sectionPoint K A t x ∈ (d i).locus) ↔
      ∃ j, x ∈ ((rationalFamilyPullbackCharts K t d).2 j).locus :=
  (exists_finite_family_rational_pullback K t d).choose_spec.choose_spec x

/-- If the annulus charts lie in the lifted domain, each of their flattened
rational pullbacks lies in the original domain. -/
theorem rationalFamilyPullbackCharts_subset {I : Type v} [Fintype I]
    (U : Domain K A) (d : I → RationalChart K (algebra K A t))
    (h : ∀ i, (d i).locus ⊆ (liftedDomain K t U).locus)
    (j : Fin (rationalFamilyPullbackCharts K t d).1) :
    ((rationalFamilyPullbackCharts K t d).2 j).locus ⊆ U.locus := by
  intro x hx
  obtain ⟨i, hi⟩ := (mem_rationalFamilyPullbackCharts K t d x).mpr ⟨j, hx⟩
  rw [← preimage_gaussSection_liftedDomain K t U]
  exact h i hi

/-- Full representation supplies an actual bounded restriction for each
descended chart, with the required equation over the original ambient algebra. -/
def rationalFamilyPullbackMap {I : Type v} [Fintype I]
    (U : Domain K A) (d : I → RationalChart K (algebra K A t))
    (f : ∀ i, (d i).toDomain ⟶ liftedDomain K t U)
    (j : Fin (rationalFamilyPullbackCharts K t d).1) :
    ((rationalFamilyPullbackCharts K t d).2 j).toDomain ⟶ U :=
  Domain.inclusionOfSubset _ U
    (rationalFamilyPullbackCharts_subset K t U d (fun i => (f i).subset) j)

/-- A finite ambient rational cover of the actual lifted domain descends to
a finite ambient rational cover of the original full represented domain. -/
def finiteRationalCoverDescent (U : Domain K A)
    (c : Domain.FiniteRationalCover (liftedDomain K t U)) :
    Domain.FiniteRationalCover U where
  size := (rationalFamilyPullbackCharts K t c.chart).1
  chart := (rationalFamilyPullbackCharts K t c.chart).2
  map := rationalFamilyPullbackMap K t U c.chart c.map
  covers x hx := by
    apply (mem_rationalFamilyPullbackCharts K t c.chart x).mp
    apply c.covers
    change x ∈ gaussSection K A t ⁻¹' (liftedDomain K t U).locus
    rwa [preimage_gaussSection_liftedDomain]

/-- The continuous Gauss section restricted to the represented domain loci. -/
def domainGaussSection (U : Domain K A) :
    C(U.locus, (liftedDomain K t U).locus) where
  toFun x := ⟨gaussSection K A t x.val,
    (Set.ext_iff.mp (preimage_gaussSection_liftedDomain K t U) x.val).mpr x.property⟩
  continuous_toFun :=
    ((gaussSection K A t).continuous.comp continuous_subtype_val).subtype_mk _

/-- Finite unions of local rational neighborhoods descend along the continuous
Gauss section; no single pulled-back chart is asserted to be a neighborhood. -/
def finiteRationalNeighborhoodDescent (U : Domain K A) (x : U.locus)
    (N : Domain.FiniteRationalNeighborhood (liftedDomain K t U)
      (domainGaussSection K t U x)) :
    Domain.FiniteRationalNeighborhood U x :=
  Domain.FiniteRationalNeighborhood.ofPreimage
    (domainGaussSection K t U) (domainGaussSection K t U).continuous
    (Subtype.val ⁻¹' ⋃ i, (N.chart i).locus) N.mem_nhds
    (rationalFamilyPullbackCharts K t N.chart).1
    (rationalFamilyPullbackCharts K t N.chart).2
    (rationalFamilyPullbackMap K t U N.chart N.map) (by
      ext y
      simpa only [Set.mem_preimage, domainGaussSection, ContinuousMap.coe_mk,
        Set.mem_iUnion, gaussSection_apply] using
        mem_rationalFamilyPullbackCharts K t N.chart y.val)

/-- A local single-chart neighborhood upstairs also gives a finite-union
rational neighborhood downstairs. -/
def rationalNeighborhoodDescent (U : Domain K A) (x : U.locus)
    (N : Domain.RationalNeighborhood (liftedDomain K t U)
      (domainGaussSection K t U x)) :
    Domain.FiniteRationalNeighborhood U x :=
  finiteRationalNeighborhoodDescent K t U x
    (Domain.FiniteRationalNeighborhood.single N)

end Langlands.Analytic.RelativeLaurentAnnulus
