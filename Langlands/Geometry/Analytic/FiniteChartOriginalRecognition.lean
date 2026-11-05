import Langlands.Geometry.Analytic.FiniteChartGluingSpectrum
import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBoundedMapGluing

/-! # Finite-chart equalizers recover original chart algebras -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open Set Topology CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d : FiniteChartGluingData a) (parent : a.Index)
  (hcover : d.locus = Set.range (a.chart parent))

include hcover in
/-- Each selected chart is actually contained in the given original parent. -/
theorem member_subset_parent (i : Fin d.size) :
    Set.range (a.chart (d.index i)) ⊆ Set.range (a.chart parent) := by
  rw [← hcover]
  exact Set.subset_iUnion (fun j => Set.range (a.chart (d.index j))) i

/-- The original bounded restrictions give an actual finite full-domain
cover of the entire parent algebra. -/
def parentDomainCover : Domain.FiniteCover (Domain.whole K (a.algebra parent)) where
  size := d.size
  obj i := a.restrictionDomain (d.index i) parent (d.member_subset_parent parent hcover i)
  map i := ⟨a.restriction (d.index i) parent (d.member_subset_parent parent hcover i),
    BoundedAlgHom.comp_id _⟩
  covers x _ := by
    have hx : a.chart parent x ∈ d.locus := hcover.symm ▸ Set.mem_range_self x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi⟩

/-- Pairwise equalizer equations imply compatibility on every actual full
domain test, by factoring that test through the represented overlap. -/
theorem parentDomainCover_projection_compatible :
    (d.parentDomainCover parent hcover).BoundedMapCompatible d.projection := by
  dsimp only [Domain.FiniteCover.BoundedMapCompatible, parentDomainCover]
  intro i j W p q
  let O := a.restrictionDomain (d.overlap i j) parent
    ((d.overlap_subset_left i j).trans (d.member_subset_parent parent hcover i))
  let r : W ⟶ O := Domain.inclusionOfSubset W O (by
    intro x hx
    change a.chart parent x ∈ Set.range (a.chart (d.overlap i j))
    rw [d.overlap_range i j]
    exact ⟨p.subset hx, q.subset hx⟩)
  let ol : O ⟶ (d.parentDomainCover parent hcover).obj i :=
    ⟨d.leftRestriction i j,
      (a.restriction_comp _ _ _ _ _ _).symm⟩
  let or : O ⟶ (d.parentDomainCover parent hcover).obj j :=
    ⟨d.rightRestriction i j,
      (a.restriction_comp _ _ _ _ _ _).symm⟩
  have hp : p.restriction = r.restriction.comp (d.leftRestriction i j) :=
    congrArg Domain.Inclusion.restriction
      (@Subsingleton.elim (Domain.Inclusion W _) inferInstance p (r ≫ ol))
  have hq : q.restriction = r.restriction.comp (d.rightRestriction i j) :=
    congrArg Domain.Inclusion.restriction
      (@Subsingleton.elim (Domain.Inclusion W _) inferInstance q (r ≫ or))
  rw [hp, hq]
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra O.algebra =>
    r.restriction.comp f) (d.projection_overlap i j)

/-- The actual bounded map from the constructed equalizer back to the
unchanged parent algebra, obtained by finite full-domain descent. -/
def glueToParent : BoundedAlgHom K d.SectionAlgebra (a.algebra parent) :=
  (d.parentDomainCover parent hcover).glueBoundedAlgHom d.projection
    (d.parentDomainCover_projection_compatible parent hcover)

@[simp]
theorem restriction_comp_glueToParent (i : Fin d.size) :
    (a.restriction (d.index i) parent (d.member_subset_parent parent hcover i)).comp
        (d.glueToParent parent hcover) = d.projection i :=
  (d.parentDomainCover parent hcover).restriction_comp_glueBoundedAlgHom _ _ i

/-- The full original restriction family satisfies the equalizer equations. -/
theorem parentRestrictions_compatible :
    d.MapCompatible (fun i =>
      a.restriction (d.index i) parent (d.member_subset_parent parent hcover i)) := by
  intro i j
  have ho := (d.overlap_subset_left i j).trans (d.member_subset_parent parent hcover i)
  exact (a.restriction_comp _ _ _ _ _ ho).symm.trans
    (a.restriction_comp _ _ _ _ _ ho)

/-- Restrict the original parent algebra into the actual section equalizer. -/
def restrictFromParent : BoundedAlgHom K (a.algebra parent) d.SectionAlgebra :=
  d.lift _ (d.parentRestrictions_compatible parent hcover)

@[simp]
theorem projection_comp_restrictFromParent (i : Fin d.size) :
    (d.projection i).comp (d.restrictFromParent parent hcover) =
      a.restriction (d.index i) parent (d.member_subset_parent parent hcover i) := rfl

/-- Full-domain algebra separation proves recovery of all parent elements,
including information invisible on spectrum points. -/
theorem glueToParent_restrictFromParent (b : a.algebra parent) :
    d.glueToParent parent hcover (d.restrictFromParent parent hcover b) = b := by
  apply (d.parentDomainCover parent hcover).algebra_ext_of_restrict_eq
  intro i
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index i)) =>
    f (d.restrictFromParent parent hcover b))
    (d.restriction_comp_glueToParent parent hcover i)

theorem restrictFromParent_glueToParent (s : d.SectionAlgebra) :
    d.restrictFromParent parent hcover (d.glueToParent parent hcover s) = s := by
  apply d.section_ext
  intro i
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index i)) => f s)
    (d.restriction_comp_glueToParent parent hcover i)

/-- The constructed equalizer recovers the original affinoid algebra with
bounded maps in both directions, rather than an assumed affinoid output. -/
def parentAlgEquiv : BoundedAlgEquiv K (a.algebra parent) d.SectionAlgebra :=
  BoundedAlgEquiv.ofHomInv (d.restrictFromParent parent hcover)
    (d.glueToParent parent hcover) (d.glueToParent_restrictFromParent parent hcover)
    (d.restrictFromParent_glueToParent parent hcover)

/-- The literal union has the original parent spectrum topology. -/
def parentHomeomorph : d.locus ≃ₜ BanachSpectrum (a.algebra parent) :=
  (Homeomorph.setCongr hcover).trans (a.isEmbedding_chart parent).toHomeomorph.symm

@[simp]
theorem parentHomeomorph_componentMap (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    d.parentHomeomorph parent hcover (d.componentMap i x) =
      BanachSpectrum.comap
        (a.restriction (d.index i) parent
          (d.member_subset_parent parent hcover i)).toBoundedRingHom x := by
  apply (a.isEmbedding_chart parent).injective
  calc
    a.chart parent (d.parentHomeomorph parent hcover (d.componentMap i x)) =
        a.chart (d.index i) x :=
      congrArg Subtype.val ((a.isEmbedding_chart parent).toHomeomorph.apply_symm_apply
        ((Homeomorph.setCongr hcover) (d.componentMap i x)))
    _ = _ := (a.restriction_chart _ _ _ x).symm

/-- The global pointwise map is precisely the homeomorphism induced by the
constructed bounded algebra equivalence and the original parent chart. -/
theorem spectrumMap_eq_parent (x : d.locus) :
    d.spectrumMap x = (d.parentAlgEquiv parent hcover).spectrumHomeomorph.symm
      (d.parentHomeomorph parent hcover x) := by
  obtain ⟨⟨i, y⟩, rfl⟩ := d.totalMap_surjective x
  change d.spectrumMap (d.componentMap i y) =
    (d.parentAlgEquiv parent hcover).spectrumHomeomorph.symm
      (d.parentHomeomorph parent hcover (d.componentMap i y))
  rw [d.spectrumMap_componentMap, d.parentHomeomorph_componentMap]
  apply BanachSpectrum.ext
  intro s
  exact (congrArg (fun f : BoundedAlgHom K d.SectionAlgebra
    (a.algebra (d.index i)) => y (f s))
    (d.restriction_comp_glueToParent parent hcover i)).symm

/-- The canonical finite-union spectrum map is an actual homeomorphism
whenever the union is an original chart, proved from algebra descent. -/
def originalSpectrumHomeomorph : d.locus ≃ₜ BanachSpectrum d.SectionAlgebra :=
  (d.parentHomeomorph parent hcover).trans
    (d.parentAlgEquiv parent hcover).spectrumHomeomorph.symm

@[simp]
theorem originalSpectrumHomeomorph_apply (x : d.locus) :
    d.originalSpectrumHomeomorph parent hcover x = d.spectrumMap x :=
  (d.spectrumMap_eq_parent parent hcover x).symm

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
