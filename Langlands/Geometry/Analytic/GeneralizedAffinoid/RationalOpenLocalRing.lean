import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenStalkResidue
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Local rings of the actual ordinary-open affinoid sheaf -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory TopologicalSpace Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- Rational interior sections commute with the original bounded restrictions. -/
theorem chartInteriorSection_restriction {d e : RationalChart K A} (f : e ⟶ d)
    (a : d.algebra) :
    OpenSections.restriction (interior_mono f.subset) (chartInteriorSection d a) =
      chartInteriorSection e (f.restriction a) := by
  apply OpenSections.ext
  intro t
  exact congrArg (fun g : t.val ⟶ d => g.restriction a)
    (@Subsingleton.elim (Restriction t.val d) inferInstance
      (restrictionOfSubset t.val d
        ((t.property.trans (interior_mono f.subset)).trans interior_subset))
      (restrictionOfSubset t.val e (t.property.trans interior_subset) ≫ f))

/-- Topological germs of rational representatives respect actual restrictions. -/
theorem chartOpenGerm_restriction {d e : RationalChart K A} (f : e ⟶ d)
    (x : BanachSpectrum A) (he : x ∈ interior e.locus)
    (hd : x ∈ interior d.locus) (a : d.algebra) :
    chartOpenGerm e x he (f.restriction a) = chartOpenGerm d x hd a := by
  change openGerm (interiorOpen e) x he (chartInteriorSection e (f.restriction a)) = _
  rw [← chartInteriorSection_restriction f a]
  exact TopCat.Presheaf.germ_res_apply (X := TopCat.of (BanachSpectrum A))
    (openAlgebraPresheaf K A) (U := interiorOpen e) (V := interiorOpen d)
      (homOfLE (interior_mono f.subset)) x he (chartInteriorSection d a)

omit [CompleteSpace K] in
/-- A relative rational neighborhood of an interior point is an actual
ambient rational neighborhood. -/
theorem RelativeNeighborhood.mem_ambient_nhds (d : RationalChart K A)
    (x : BanachSpectrum A) (hx : x ∈ interior d.locus) (W : Set d.locus)
    (N : RelativeNeighborhood d ⟨x, interior_subset hx⟩ W) :
    N.chart.locus ∈ 𝓝 x := by
  obtain ⟨V, hV, hsub⟩ :=
    (mem_nhds_subtype d.locus ⟨x, interior_subset hx⟩ _).mp N.mem_nhds
  apply Filter.mem_of_superset
    (Filter.inter_mem hV (mem_interior_iff_mem_nhds.mp hx))
  intro z hz
  exact hsub (show (⟨z, hz.2⟩ : d.locus) ∈ Subtype.val ⁻¹' V from hz.1)

/-- Nonvanishing at the actual chart point gives an invertible restriction
on a smaller actual rational neighborhood, including nilpotent algebras. -/
theorem exists_isUnit_restriction (d : RationalChart K A) (x : BanachSpectrum A)
    (hx : x ∈ interior d.locus) (a : d.algebra)
    (ha : d.locusHomeomorph.symm ⟨x, interior_subset hx⟩ a ≠ 0) :
    ∃ (e : RationalChart K A) (f : e ⟶ d),
      x ∈ interior e.locus ∧ IsUnit (f.restriction a) := by
  let W : Set d.locus := {z | d.locusHomeomorph.symm z a ≠ 0}
  have hW : IsOpen W :=
    isOpen_compl_singleton.preimage
      ((BanachSpectrum.evaluation a).continuous.comp d.locusHomeomorph.symm.continuous)
  let N := RelativeNeighborhood.ofNeighborhood d ⟨x, interior_subset hx⟩ W
    (hW.mem_nhds ha)
  refine ⟨N.chart, N.map, mem_interior_iff_mem_nhds.mpr
    (N.mem_ambient_nhds d x hx W), ?_⟩
  apply (isUnit_iff_forall_spectrum_ne_zero N.chart.algebra _).mpr
  intro y
  have hy : N.map.locusMap (N.chart.locusHomeomorph y) ∈ W :=
    N.subordinate (N.chart.locusHomeomorph y).property
  change (d.locusHomeomorph.symm
    (N.map.locusMap (N.chart.locusHomeomorph y))) a ≠ 0 at hy
  rw [← N.map.locusHomeomorph_naturality, Homeomorph.symm_apply_apply] at hy
  exact hy

/-- An actual rational neighborhood equipped with a unit representing
the restriction of the specified original quotient element. -/
structure UnitNeighborhood (d : RationalChart K A) (x : BanachSpectrum A)
    (a : d.algebra) where
  chart : RationalChart K A
  map : chart ⟶ d
  mem_interior : x ∈ interior chart.locus
  unit : chart.algebraˣ
  unit_eq : (unit : chart.algebra) = map.restriction a

/-- Construct an actual unit on an actual smaller rational neighborhood
from nonvanishing of the chart seminorm at an interior point. -/
def unitNeighborhood (d : RationalChart K A) (x : BanachSpectrum A)
    (hx : x ∈ interior d.locus) (a : d.algebra)
    (ha : d.locusHomeomorph.symm ⟨x, interior_subset hx⟩ a ≠ 0) :
    UnitNeighborhood d x a := by
  apply Classical.choice
  obtain ⟨e, f, he, hu⟩ := exists_isUnit_restriction d x hx a ha
  exact ⟨⟨e, f, he, hu.unit, hu.unit_spec⟩⟩

/-- An actual point makes its ordinary-open stalk a nonzero algebra. -/
instance openStalk_nontrivial (x : BanachSpectrum A) : Nontrivial (openStalk x) :=
  (openStalkResidue x).hom.toRingHom.domain_nontrivial

/-- A genuine topological germ is a unit exactly when its constructed
completed-residue evaluation is nonzero. -/
theorem isUnit_iff_openStalkResidue_ne_zero (x : BanachSpectrum A)
    (t : openStalk x) : IsUnit t ↔ openStalkResidue x t ≠ 0 := by
  constructor
  · intro ht
    exact (ht.map (openStalkResidue x).hom.toRingHom).ne_zero
  · intro ht
    obtain ⟨d, hx, a, rfl⟩ := exists_chartOpenGerm x t
    have ha : d.locusHomeomorph.symm ⟨x, interior_subset hx⟩ a ≠ 0 := by
      rw [openStalkResidue_chartOpenGerm] at ht
      rw [← norm_completedResidueEvaluation d x (interior_subset hx) a]
      exact norm_ne_zero_iff.mpr ht
    obtain ⟨e, f, he, hu⟩ := exists_isUnit_restriction d x hx a ha
    rw [← chartOpenGerm_restriction f x he hx a]
    exact hu.map (chartOpenGerm e x he).toRingHom

/-- Locality is proved for the genuine ordinary-open stalk. -/
instance openStalk_isLocalRing (x : BanachSpectrum A) : IsLocalRing (openStalk x) := by
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  change ¬ IsUnit (a + b)
  intro hab
  apply (isUnit_iff_openStalkResidue_ne_zero x (a + b)).mp hab
  have ha' : openStalkResidue x a = 0 := by
    by_contra h
    exact ha ((isUnit_iff_openStalkResidue_ne_zero x a).mpr h)
  have hb' : openStalkResidue x b = 0 := by
    by_contra h
    exact hb ((isUnit_iff_openStalkResidue_ne_zero x b).mpr h)
  rw [map_add, ha', hb', add_zero]

/-- The prime evaluation kernel is exactly the maximal ideal of the
constructed local ring. -/
theorem openStalkResidueKernel_eq_maximalIdeal (x : BanachSpectrum A) :
    openStalkResidueKernel x = IsLocalRing.maximalIdeal (openStalk x) := by
  ext t
  rw [IsLocalRing.mem_maximalIdeal]
  change openStalkResidue x t = 0 ↔ ¬ IsUnit t
  rw [isUnit_iff_openStalkResidue_ne_zero]
  exact not_not.symm

instance openStalkResidueKernel_isMaximal (x : BanachSpectrum A) :
    (openStalkResidueKernel x).IsMaximal := by
  rw [openStalkResidueKernel_eq_maximalIdeal]
  infer_instance

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
