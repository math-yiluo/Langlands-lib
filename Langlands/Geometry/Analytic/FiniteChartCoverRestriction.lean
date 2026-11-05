import Langlands.Geometry.Analytic.FiniteChartGluingAlgebra
import Langlands.Geometry.Analytic.AtlasDomainRestrictionNaturality

/-! # Bounded restrictions of finite-chart sections by subordinate covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d : FiniteChartGluingData a)

/-- Restrict an equalizer section to an actual full domain inside one selected
member, retaining the entire bounded algebra map. -/
def memberDomainRestriction (k : a.Index) (U : Domain K (a.algebra k))
    (i : Fin d.size) (hi : a.chart k '' U.locus ⊆ Set.range (a.chart (d.index i))) :
    BoundedAlgHom K d.SectionAlgebra U.algebra :=
  (a.domainChartRestriction k (d.index i) U hi).comp (d.projection i)

/-- On any full-domain test contained in two members, both formulas agree
by the represented overlap and its original restriction equations. -/
theorem memberDomainRestriction_eq (k : a.Index) (U : Domain K (a.algebra k))
    (i j : Fin d.size)
    (hi : a.chart k '' U.locus ⊆ Set.range (a.chart (d.index i)))
    (hj : a.chart k '' U.locus ⊆ Set.range (a.chart (d.index j))) :
    d.memberDomainRestriction k U i hi = d.memberDomainRestriction k U j hj := by
  have ho : a.chart k '' U.locus ⊆ Set.range (a.chart (d.overlap i j)) := by
    rw [d.overlap_range]
    exact fun x hx => ⟨hi hx, hj hx⟩
  have hl := a.domainChartRestriction_comp_original k (d.overlap i j) (d.index i)
    U ho hi (d.overlap_subset_left i j)
  have hr := a.domainChartRestriction_comp_original k (d.overlap i j) (d.index j)
    U ho hj (d.overlap_subset_right i j)
  unfold memberDomainRestriction
  rw [← hl, ← hr]
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra
    (a.algebra (d.overlap i j)) => (a.domainChartRestriction k _ U ho).comp f)
    (d.projection_overlap i j)

/-- Full-domain inclusions commute with the member restriction formula. -/
theorem memberDomainRestriction_naturality (k : a.Index)
    {U V : Domain K (a.algebra k)} (p : V ⟶ U) (i : Fin d.size)
    (hi : a.chart k '' U.locus ⊆ Set.range (a.chart (d.index i)))
    (hV : a.chart k '' V.locus ⊆ Set.range (a.chart (d.index i))) :
    p.restriction.comp (d.memberDomainRestriction k U i hi) =
      d.memberDomainRestriction k V i hV :=
  congrArg (fun f : BoundedAlgHom K (a.algebra (d.index i)) V.algebra =>
    f.comp (d.projection i))
    (a.domainChartRestriction_naturality k (d.index i) p hi hV)

/-- Explicit finite original charts cover the original parent and are each
contained in one chosen member of the section equalizer. -/
structure SubordinateChartCover (parent : a.Index) where
  size : ℕ
  index : Fin size → a.Index
  member : Fin size → Fin d.size
  subset_parent : ∀ t, Set.range (a.chart (index t)) ⊆ Set.range (a.chart parent)
  subset_member : ∀ t,
    Set.range (a.chart (index t)) ⊆ Set.range (a.chart (d.index (member t)))
  covers : Set.range (a.chart parent) ⊆ ⋃ t, Set.range (a.chart (index t))

namespace SubordinateChartCover

variable {d} {parent : a.Index} (c : d.SubordinateChartCover parent)

/-- These subordinate original charts form an actual finite full-domain
cover of the unchanged parent algebra. -/
def domainCover : Domain.FiniteCover (Domain.whole K (a.algebra parent)) where
  size := c.size
  obj t := a.restrictionDomain (c.index t) parent (c.subset_parent t)
  map t := ⟨a.restriction (c.index t) parent (c.subset_parent t),
    BoundedAlgHom.comp_id _⟩
  covers x _ := by
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (c.covers (Set.mem_range_self x))
    exact ⟨t, ht⟩

theorem domainCover_member_image (t : Fin c.size) :
    a.chart parent '' (c.domainCover.obj t).locus ⊆
      Set.range (a.chart (d.index (c.member t))) := by
  rintro _ ⟨x, hx, rfl⟩
  exact c.subset_member t hx

/-- Each local map is constructed from the original bounded restriction and
an actual equalizer projection. -/
def localRestriction (t : Fin c.size) :
    BoundedAlgHom K d.SectionAlgebra (a.algebra (c.index t)) :=
  (a.restriction (c.index t) (d.index (c.member t)) (c.subset_member t)).comp
    (d.projection (c.member t))

theorem localRestriction_eq_memberDomainRestriction (t : Fin c.size) :
    c.localRestriction t =
      d.memberDomainRestriction parent (c.domainCover.obj t) (c.member t)
        (c.domainCover_member_image t) := by
  unfold memberDomainRestriction
  rw [a.domainChartRestriction_of_commonChart parent (d.index (c.member t))
    (c.index t) (c.domainCover.obj t) (c.domainCover_member_image t)
    (c.subset_parent t) (c.subset_member t) (𝟙 (c.domainCover.obj t))]
  rfl

/-- Local maps agree after every actual full-domain test into two members
of the constructed cover. -/
theorem localRestriction_compatible :
    c.domainCover.BoundedMapCompatible c.localRestriction := by
  intro t s W p q
  have ht : a.chart parent '' W.locus ⊆
      Set.range (a.chart (d.index (c.member t))) := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.subset_member t (p.subset hx)
  have hs : a.chart parent '' W.locus ⊆
      Set.range (a.chart (d.index (c.member s))) := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.subset_member s (q.subset hx)
  rw [c.localRestriction_eq_memberDomainRestriction t,
    c.localRestriction_eq_memberDomainRestriction s,
    d.memberDomainRestriction_naturality parent p _ _ ht,
    d.memberDomainRestriction_naturality parent q _ _ hs]
  exact d.memberDomainRestriction_eq parent W _ _ ht hs

/-- The actual bounded restriction to the parent chart is obtained by finite
full-domain descent; no output map is part of the cover data. -/
def restriction : BoundedAlgHom K d.SectionAlgebra (a.algebra parent) :=
  c.domainCover.glueBoundedAlgHom c.localRestriction c.localRestriction_compatible

@[simp]
theorem original_comp_restriction (t : Fin c.size) :
    (a.restriction (c.index t) parent (c.subset_parent t)).comp c.restriction =
      c.localRestriction t :=
  c.domainCover.restriction_comp_glueBoundedAlgHom _ _ t

/-- Pull the finite original-chart cover back to an arbitrary actual
full domain, using the already constructed full-domain intersections. -/
def intersectionCover (W : Domain K (a.algebra parent)) : Domain.FiniteCover W where
  size := c.size
  obj t := W.inter (c.domainCover.obj t)
  map t := Domain.interLeft W (c.domainCover.obj t)
  covers x hx := by
    obtain ⟨t, ht⟩ := c.domainCover.covers x (Set.mem_univ x)
    exact ⟨t, hx, ht⟩

/-- The descended map recovers the restriction formula on every full-domain
test whose ambient image lies in any selected member. -/
theorem restriction_test (W : Domain K (a.algebra parent)) (j : Fin d.size)
    (hj : a.chart parent '' W.locus ⊆ Set.range (a.chart (d.index j))) :
    W.baseMap.comp c.restriction = d.memberDomainRestriction parent W j hj := by
  apply BoundedAlgHom.ext
  intro b
  apply (c.intersectionCover W).algebra_ext_of_restrict_eq
  intro t
  let T := W.inter (c.domainCover.obj t)
  let L := Domain.interLeft W (c.domainCover.obj t)
  let R := Domain.interRight W (c.domainCover.obj t)
  have ht : a.chart parent '' T.locus ⊆
      Set.range (a.chart (d.index (c.member t))) := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.subset_member t (R.subset hx)
  have hjT : a.chart parent '' T.locus ⊆ Set.range (a.chart (d.index j)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hj ⟨x, L.subset hx, rfl⟩
  have h₁ := congrArg (fun f : BoundedAlgHom K (a.algebra parent) T.algebra =>
    f.comp c.restriction) (L.comp_baseMap.trans R.comp_baseMap.symm)
  have h₂ := congrArg (fun f : BoundedAlgHom K d.SectionAlgebra
    (c.domainCover.obj t).algebra => R.restriction.comp f)
    (c.original_comp_restriction t)
  have h₃ : R.restriction.comp (c.localRestriction t) =
      d.memberDomainRestriction parent T (c.member t) ht := by
    exact (congrArg (fun f : BoundedAlgHom K d.SectionAlgebra
      (c.domainCover.obj t).algebra => R.restriction.comp f)
      (c.localRestriction_eq_memberDomainRestriction t)).trans
        (d.memberDomainRestriction_naturality parent R _ _ ht)
  have h₄ := d.memberDomainRestriction_eq parent T (c.member t) j ht hjT
  have h₅ := d.memberDomainRestriction_naturality parent L j hj hjT
  have heq :
      ((c.intersectionCover W).map t).restriction.comp
          (W.baseMap.comp c.restriction) =
        ((c.intersectionCover W).map t).restriction.comp
          (d.memberDomainRestriction parent W j hj) :=
    (((h₁.trans h₂).trans h₃).trans h₄).trans h₅.symm
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra
    ((c.intersectionCover W).obj t).algebra => f b) heq

/-- Every original chart contained in the parent and any selected member
recovers its original bounded restriction of the corresponding projection. -/
theorem restriction_original (k : a.Index)
    (hkp : Set.range (a.chart k) ⊆ Set.range (a.chart parent)) (i : Fin d.size)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart (d.index i))) :
    (a.restriction k parent hkp).comp c.restriction =
      (a.restriction k (d.index i) hki).comp (d.projection i) := by
  let U := a.restrictionDomain k parent hkp
  have hU : a.chart parent '' U.locus ⊆ Set.range (a.chart (d.index i)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hki hx
  have h := a.domainChartRestriction_of_commonChart parent (d.index i) k U hU
    hkp hki (𝟙 U)
  exact (c.restriction_test U i hU).trans
    (congrArg (fun f : BoundedAlgHom K (a.algebra (d.index i)) U.algebra =>
      f.comp (d.projection i)) h)

/-- A bounded map is determined by its local original-chart formulas. -/
theorem restriction_unique (f : BoundedAlgHom K d.SectionAlgebra (a.algebra parent))
    (hf : ∀ t, (a.restriction (c.index t) parent (c.subset_parent t)).comp f =
      c.localRestriction t) : f = c.restriction :=
  c.domainCover.glueBoundedAlgHom_unique _ _ f hf

/-- Two unrelated finite subordinate covers construct the same full bounded
map to the original parent algebra. -/
theorem restriction_eq (e : d.SubordinateChartCover parent) :
    c.restriction = e.restriction := by
  apply (c.restriction_unique e.restriction _).symm
  intro t
  exact (e.restriction_test (c.domainCover.obj t) (c.member t)
    (c.domainCover_member_image t)).trans
      (c.localRestriction_eq_memberDomainRestriction t).symm

/-- Restrictions for original-chart inclusions commute with descent even
when the two charts use unrelated subordinate covers. -/
theorem restriction_naturality {child : a.Index}
    (e : d.SubordinateChartCover child)
    (h : Set.range (a.chart child) ⊆ Set.range (a.chart parent)) :
    (a.restriction child parent h).comp c.restriction = e.restriction := by
  apply e.restriction_unique
  intro t
  have htp := (e.subset_parent t).trans h
  have h₁ := congrArg (fun f : BoundedAlgHom K (a.algebra parent)
    (a.algebra (e.index t)) => f.comp c.restriction)
    (a.restriction_comp (e.index t) child parent (e.subset_parent t) h htp).symm
  exact h₁.trans
    (c.restriction_original (e.index t) htp (e.member t) (e.subset_member t))

/-- If the entire parent lies in one member, descent recovers the original
bounded restriction followed by that member's equalizer projection. -/
theorem restriction_of_member (i : Fin d.size)
    (h : Set.range (a.chart parent) ⊆ Set.range (a.chart (d.index i))) :
    c.restriction =
      (a.restriction parent (d.index i) h).comp (d.projection i) := by
  have heq := c.restriction_original parent Subset.rfl i h
  rwa [a.restriction_id, BoundedAlgHom.id_comp] at heq

end SubordinateChartCover

/-- Represented cross intersections construct a subordinate cover, provided
the original parent is contained in the literal union. -/
def subordinateCoverOfIntersections (parent : a.Index)
    (hparent : Set.range (a.chart parent) ⊆ d.locus)
    (cross : Fin d.size → a.Index)
    (hcross : ∀ i, Set.range (a.chart (cross i)) =
      Set.range (a.chart parent) ∩ Set.range (a.chart (d.index i))) :
    d.SubordinateChartCover parent where
  size := d.size
  index := cross
  member := id
  subset_parent i := by rw [hcross]; exact Set.inter_subset_left
  subset_member i := by rw [hcross]; exact Set.inter_subset_right
  covers x hx := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hparent hx)
    apply Set.mem_iUnion.mpr
    exact ⟨i, (hcross i).symm ▸ ⟨hx, hi⟩⟩

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
