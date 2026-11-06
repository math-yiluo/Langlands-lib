import Langlands.Geometry.Analytic.FiniteChartOriginalRecognition
import Langlands.Geometry.Analytic.IntrinsicAffinoidAlgebra

/-! # Full section-algebra recovery for actual finite affinoid realizations -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open Set Topology CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d : FiniteChartGluingData a)

/-- An actual presented affinoid chart on the finite union, with full
component representations and compatibility of the entire bounded maps.
No comparison with the section equalizer is supplied. -/
structure AffinoidRealization where
  algebra : PresentedAffinoidAlgebra K
  chart : C(BanachSpectrum algebra, X)
  isEmbedding_chart : IsEmbedding chart
  range_chart : Set.range chart = d.locus
  restriction : ∀ i : Fin d.size, BoundedAlgHom K algebra (a.algebra (d.index i))
  restriction_chart : ∀ i x,
    chart (BanachSpectrum.comap (restriction i).toBoundedRingHom x) =
      a.chart (d.index i) x
  represents : ∀ i, Represents K (restriction i)
    (chart ⁻¹' Set.range (a.chart (d.index i)))
  compatible : d.MapCompatible restriction

namespace AffinoidRealization

variable {d} (c : d.AffinoidRealization)

def componentDomain (i : Fin d.size) : Domain K c.algebra where
  algebra := a.algebra (d.index i)
  baseMap := c.restriction i
  locus := c.chart ⁻¹' Set.range (a.chart (d.index i))
  represents := c.represents i

/-- The component algebras give an actual full-domain cover of the
unchanged parent presentation. -/
def domainCover : Domain.FiniteCover (Domain.whole K c.algebra) where
  size := d.size
  obj := c.componentDomain
  map i := ⟨c.restriction i, BoundedAlgHom.comp_id _⟩
  covers x _ := by
    have hx : c.chart x ∈ d.locus := c.range_chart ▸ Set.mem_range_self x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi⟩

/-- Compose the first component's full representation with the actual
original overlap restriction. Its image is the literal relative overlap. -/
theorem overlap_represents (i j : Fin d.size) :
    Represents K ((d.leftRestriction i j).comp (c.restriction i))
      (c.chart ⁻¹' Set.range (a.chart (d.overlap i j))) := by
  have hr := (c.represents i).comp
    (a.restriction_represents (d.overlap i j) (d.index i) (d.overlap_subset_left i j))
  have heq :
      BanachSpectrum.comap (c.restriction i).toBoundedRingHom ''
        (a.chart (d.index i) ⁻¹' Set.range (a.chart (d.overlap i j))) =
      c.chart ⁻¹' Set.range (a.chart (d.overlap i j)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change c.chart (BanachSpectrum.comap (c.restriction i).toBoundedRingHom y) ∈
        Set.range (a.chart (d.overlap i j))
      rw [c.restriction_chart i y]
      exact hy
    · rintro ⟨y, hy⟩
      let z := BanachSpectrum.comap (d.leftRestriction i j).toBoundedRingHom y
      refine ⟨z, ?_, ?_⟩
      · change a.chart (d.index i)
          (BanachSpectrum.comap (d.leftRestriction i j).toBoundedRingHom y) ∈
            Set.range (a.chart (d.overlap i j))
        exact ⟨y, (a.restriction_chart _ _ _ y).symm⟩
      · apply c.isEmbedding_chart.injective
        rw [c.restriction_chart]
        exact (a.restriction_chart _ _ _ y).trans hy
  exact heq ▸ hr

def overlapDomain (i j : Fin d.size) : Domain K c.algebra where
  algebra := a.algebra (d.overlap i j)
  baseMap := (d.leftRestriction i j).comp (c.restriction i)
  locus := c.chart ⁻¹' Set.range (a.chart (d.overlap i j))
  represents := c.overlap_represents i j

/-- The equalizer equations imply agreement after every actual domain
test into any pair of components. This is full algebraic compatibility. -/
theorem projection_compatible :
    c.domainCover.BoundedMapCompatible d.projection := by
  dsimp only [Domain.FiniteCover.BoundedMapCompatible, domainCover]
  intro i j W p q
  let O := c.overlapDomain i j
  let r : W ⟶ O := Domain.inclusionOfSubset W O (by
    intro x hx
    change c.chart x ∈ Set.range (a.chart (d.overlap i j))
    rw [d.overlap_range]
    exact ⟨p.subset hx, q.subset hx⟩)
  let ol : O ⟶ c.domainCover.obj i := ⟨d.leftRestriction i j, rfl⟩
  let or : O ⟶ c.domainCover.obj j :=
    ⟨d.rightRestriction i j, (c.compatible i j).symm⟩
  have hp : p.restriction = r.restriction.comp (d.leftRestriction i j) :=
    congrArg Domain.Inclusion.restriction
      (@Subsingleton.elim (Domain.Inclusion W _) inferInstance p (r ≫ ol))
  have hq : q.restriction = r.restriction.comp (d.rightRestriction i j) :=
    congrArg Domain.Inclusion.restriction
      (@Subsingleton.elim (Domain.Inclusion W _) inferInstance q (r ≫ or))
  rw [hp, hq]
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra O.algebra =>
    r.restriction.comp f) (d.projection_overlap i j)

/-- Finite full-domain descent constructs the entire bounded map from
the actual Banach equalizer back to the original parent algebra. -/
def glueToParent : BoundedAlgHom K d.SectionAlgebra c.algebra :=
  c.domainCover.glueBoundedAlgHom d.projection c.projection_compatible

@[simp]
theorem restriction_comp_glueToParent (i : Fin d.size) :
    (c.restriction i).comp c.glueToParent = d.projection i :=
  c.domainCover.restriction_comp_glueBoundedAlgHom _ _ i

def restrictFromParent : BoundedAlgHom K c.algebra d.SectionAlgebra :=
  d.lift c.restriction c.compatible

@[simp]
theorem projection_comp_restrictFromParent (i : Fin d.size) :
    (d.projection i).comp c.restrictFromParent = c.restriction i := rfl

theorem glueToParent_restrictFromParent (b : c.algebra) :
    c.glueToParent (c.restrictFromParent b) = b := by
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro i
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index i)) =>
    f (c.restrictFromParent b)) (c.restriction_comp_glueToParent i)

theorem restrictFromParent_glueToParent (s : d.SectionAlgebra) :
    c.restrictFromParent (c.glueToParent s) = s := by
  apply d.section_ext
  intro i
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index i)) =>
    f s) (c.restriction_comp_glueToParent i)

/-- Both maps and inverse identities are constructed in the original
algebras, without reconstructing maps from spectrum points. -/
def sectionAlgEquiv : BoundedAlgEquiv K c.algebra d.SectionAlgebra :=
  BoundedAlgEquiv.ofHomInv c.restrictFromParent c.glueToParent
    c.glueToParent_restrictFromParent c.restrictFromParent_glueToParent

def locusHomeomorph : d.locus ≃ₜ BanachSpectrum c.algebra :=
  (Homeomorph.setCongr c.range_chart).symm.trans c.isEmbedding_chart.toHomeomorph.symm

@[simp]
theorem locusHomeomorph_componentMap (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    c.locusHomeomorph (d.componentMap i x) =
      BanachSpectrum.comap (c.restriction i).toBoundedRingHom x := by
  apply c.isEmbedding_chart.injective
  calc
    c.chart (c.locusHomeomorph (d.componentMap i x)) = a.chart (d.index i) x :=
      congrArg Subtype.val (c.isEmbedding_chart.toHomeomorph.apply_symm_apply
        ((Homeomorph.setCongr c.range_chart).symm (d.componentMap i x)))
    _ = _ := (c.restriction_chart i x).symm

/-- The existing canonical equalizer point map is exactly the one from
the constructed bounded algebra equivalence and original chart. -/
theorem spectrumMap_eq_parent (x : d.locus) :
    d.spectrumMap x = c.sectionAlgEquiv.spectrumHomeomorph.symm (c.locusHomeomorph x) := by
  obtain ⟨⟨i, y⟩, rfl⟩ := d.totalMap_surjective x
  change d.spectrumMap (d.componentMap i y) =
    c.sectionAlgEquiv.spectrumHomeomorph.symm (c.locusHomeomorph (d.componentMap i y))
  rw [d.spectrumMap_componentMap, c.locusHomeomorph_componentMap]
  apply BanachSpectrum.ext
  intro s
  exact (congrArg (fun f : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index i)) =>
    y (f s)) (c.restriction_comp_glueToParent i)).symm

def spectrumHomeomorph : d.locus ≃ₜ BanachSpectrum d.SectionAlgebra :=
  c.locusHomeomorph.trans c.sectionAlgEquiv.spectrumHomeomorph.symm

@[simp]
theorem spectrumHomeomorph_apply (x : d.locus) :
    c.spectrumHomeomorph x = d.spectrumMap x := (c.spectrumMap_eq_parent x).symm

include c in
theorem bijective_spectrumMap : Function.Bijective d.spectrumMap := by
  have heq : d.spectrumMap = c.spectrumHomeomorph :=
    funext fun x => (c.spectrumHomeomorph_apply x).symm
  rw [heq]
  exact c.spectrumHomeomorph.bijective

include c in
/-- The unchanged Banach equalizer is intrinsically affinoid, proved from
the constructed full bounded equivalence with the actual presentation. -/
theorem isAffinoid_sectionAlgebra : IsAffinoidAlgebra K d.SectionAlgebra :=
  (PresentedAffinoidAlgebra.isAffinoidAlgebra K c.algebra).of_boundedEquiv c.sectionAlgEquiv

end AffinoidRealization

/-- Existing original-parent finite covers supply all realization data
from their actual restrictions and full universal properties. -/
def originalAffinoidRealization (parent : a.Index)
    (hcover : d.locus = Set.range (a.chart parent)) : d.AffinoidRealization where
  algebra := a.algebra parent
  chart := ⟨a.chart parent, (a.isEmbedding_chart parent).continuous⟩
  isEmbedding_chart := a.isEmbedding_chart parent
  range_chart := hcover.symm
  restriction i := a.restriction (d.index i) parent (d.member_subset_parent parent hcover i)
  restriction_chart _i x := a.restriction_chart _ _ _ x
  represents _i := a.restriction_represents _ _ _
  compatible := d.parentRestrictions_compatible parent hcover

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
