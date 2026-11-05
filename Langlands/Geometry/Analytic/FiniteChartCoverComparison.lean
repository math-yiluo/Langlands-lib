import Langlands.Geometry.Analytic.FiniteChartCoverRestriction

/-! # Bounded comparisons between finite-chart section equalizers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d e : FiniteChartGluingData a)

/-- Original charts subordinate to the source family explicitly cover every
target member and every target overlap. No comparison map is supplied. -/
structure ComparisonCover where
  member : ∀ i : Fin e.size, d.SubordinateChartCover (e.index i)
  overlap : ∀ i j : Fin e.size, d.SubordinateChartCover (e.overlap i j)

namespace ComparisonCover

variable {d e} (c : d.ComparisonCover e)

include c in
/-- Each target member lies in the actual source union. -/
theorem member_subset_locus (i : Fin e.size) :
    Set.range (a.chart (e.index i)) ⊆ d.locus := by
  intro x hx
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp ((c.member i).covers hx)
  exact Set.mem_iUnion.mpr ⟨(c.member i).member t, (c.member i).subset_member t ht⟩

include c in
theorem locus_subset : e.locus ⊆ d.locus := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact c.member_subset_locus i hi

/-- Descent to each target member satisfies both target overlap equations. -/
theorem memberRestrictions_compatible :
    e.MapCompatible (fun i => (c.member i).restriction) := by
  intro i j
  exact ((c.member i).restriction_naturality (c.overlap i j)
    (e.overlap_subset_left i j)).trans
      ((c.member j).restriction_naturality (c.overlap i j)
        (e.overlap_subset_right i j)).symm

/-- Construct the bounded comparison by lifting the descended member maps
into the actual target equalizer. -/
def comparison : BoundedAlgHom K d.SectionAlgebra e.SectionAlgebra :=
  e.lift _ c.memberRestrictions_compatible

@[simp]
theorem projection_comp_comparison (i : Fin e.size) :
    (e.projection i).comp c.comparison = (c.member i).restriction := rfl

/-- On a common original subchart, the comparison retains the entire
original bounded restriction formula. -/
theorem original_comp_projection_comparison (k : a.Index)
    (i : Fin d.size) (j : Fin e.size)
    (hkd : Set.range (a.chart k) ⊆ Set.range (a.chart (d.index i)))
    (hke : Set.range (a.chart k) ⊆ Set.range (a.chart (e.index j))) :
    (a.restriction k (e.index j) hke).comp
        ((e.projection j).comp c.comparison) =
      (a.restriction k (d.index i) hkd).comp (d.projection i) :=
  (c.member j).restriction_original k hke i hkd

/-- Unrelated subordinate-cover choices produce the same full bounded map. -/
theorem comparison_eq (c' : d.ComparisonCover e) :
    c.comparison = c'.comparison := by
  apply e.hom_ext
  intro i
  exact (c.member i).restriction_eq (c'.member i)

variable (r : e.ComparisonCover d)

include c r in
/-- Covers in both directions force equality of the literal unions. -/
theorem locus_eq : d.locus = e.locus :=
  Set.Subset.antisymm r.locus_subset c.locus_subset

/-- Separate on the reverse cover of each source member to prove the
inverse equation on every algebra element, without using spectrum points. -/
theorem comparison_comp_reverse :
    r.comparison.comp c.comparison = BoundedAlgHom.id K d.SectionAlgebra := by
  apply d.hom_ext
  intro i
  apply BoundedAlgHom.ext
  intro s
  apply (r.member i).domainCover.algebra_ext_of_restrict_eq
  intro t
  have h₁ := congrArg (fun f : BoundedAlgHom K e.SectionAlgebra
    (a.algebra ((r.member i).index t)) => f.comp c.comparison)
      ((r.member i).original_comp_restriction t)
  have h₂ := c.original_comp_projection_comparison ((r.member i).index t)
    i ((r.member i).member t) ((r.member i).subset_parent t)
    ((r.member i).subset_member t)
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra
    (a.algebra ((r.member i).index t)) => f s) (h₁.trans h₂)

/-- The actual section algebras are canonically isomorphic by explicitly
constructed bounded maps in both directions. -/
def algEquiv : BoundedAlgEquiv K d.SectionAlgebra e.SectionAlgebra :=
  BoundedAlgEquiv.ofHomInv c.comparison r.comparison
    (fun s => congrArg (fun f : BoundedAlgHom K d.SectionAlgebra d.SectionAlgebra =>
      f s) (c.comparison_comp_reverse r))
    (fun s => congrArg (fun f : BoundedAlgHom K e.SectionAlgebra e.SectionAlgebra =>
      f s) (r.comparison_comp_reverse c))

@[simp]
theorem algEquiv_toBoundedAlgHom :
    (c.algEquiv r).toBoundedAlgHom = c.comparison := rfl

@[simp]
theorem algEquiv_symm_toBoundedAlgHom :
    (c.algEquiv r).symm.toBoundedAlgHom = r.comparison := rfl

end ComparisonCover

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
