import Langlands.Geometry.Analytic.AtlasDomainRepresentation

/-! # Local characterization and naturality of unrestricted chart restrictions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

namespace CompactIntersectionChartCover

variable {a} {i j : a.Index} {U : Domain K (a.algebra i)}
  (c : a.CompactIntersectionChartCover i j (a.chart i '' U.locus))

/-- Intersections with the original cover restrict it to every contained full domain. -/
def intersectionCover (W : Domain K (a.algebra i)) (p : W ⟶ U) :
    Domain.FiniteCover W where
  size := c.size
  obj t := W.inter (c.domainCover.obj t)
  map t := Domain.interLeft W (c.domainCover.obj t)
  covers x hx := by
    obtain ⟨t, ht⟩ := c.domainCover.covers x (p.subset hx)
    exact ⟨t, hx, ht⟩

/-- Every actual local test contained in one common original chart has
the original bounded restriction formula, for any chosen finite cover. -/
theorem glueChartRestriction_test (W : Domain K (a.algebra i)) (p : W ⟶ U)
    (k : a.Index)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i))
    (hkj : Set.range (a.chart k) ⊆ Set.range (a.chart j))
    (g : W ⟶ a.restrictionDomain k i hki) :
    p.restriction.comp c.glueChartRestriction =
      g.restriction.comp (a.restriction k j hkj) := by
  apply BoundedAlgHom.ext
  intro b
  apply (c.intersectionCover W p).algebra_ext_of_restrict_eq
  intro t
  let L := Domain.interLeft W (c.domainCover.obj t)
  let R := Domain.interRight W (c.domainCover.obj t)
  have htriangle := congrArg Domain.Inclusion.restriction
    (@Subsingleton.elim (Domain.Inclusion (W.inter (c.domainCover.obj t)) U) inferInstance
      (L ≫ p) (R ≫ c.domainCover.map t))
  have h₁ := congrArg (fun q : BoundedAlgHom K U.algebra
    (W.inter (c.domainCover.obj t)).algebra => q.comp c.glueChartRestriction) htriangle
  have h₂ := congrArg (fun q : BoundedAlgHom K (a.algebra j)
    (c.domainCover.obj t).algebra => R.restriction.comp q)
    (c.restriction_comp_glueChartRestriction t)
  have h₃ := a.originalChartRestriction_overlap i j (c.index t) k
    (c.left_subset t) (c.right_subset t) hki hkj (W.inter (c.domainCover.obj t))
    (R ≫ c.domainCoverToChart t) (L ≫ g)
  have heq :
      ((c.intersectionCover W p).map t).restriction.comp
          (p.restriction.comp c.glueChartRestriction) =
        ((c.intersectionCover W p).map t).restriction.comp
          (g.restriction.comp (a.restriction k j hkj)) :=
    (h₁.trans h₂).trans h₃
  exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
    ((c.intersectionCover W p).obj t).algebra => q b) heq

/-- Any two finite common-chart covers give exactly the same bounded map. -/
theorem glueChartRestriction_eq
    (d : a.CompactIntersectionChartCover i j (a.chart i '' U.locus)) :
    c.glueChartRestriction = d.glueChartRestriction := by
  apply BoundedAlgHom.ext
  intro b
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro t
  have h := d.glueChartRestriction_test (c.domainCover.obj t) (c.domainCover.map t)
    (c.index t) (c.left_subset t) (c.right_subset t) (c.domainCoverToChart t)
  exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
    (c.domainCover.obj t).algebra => q b)
    ((c.restriction_comp_glueChartRestriction t).trans h.symm)

/-- The glued maps commute with every original full-domain inclusion,
even when the source and target use unrelated finite common-chart covers. -/
theorem glueChartRestriction_naturality {V : Domain K (a.algebra i)}
    (d : a.CompactIntersectionChartCover i j (a.chart i '' V.locus)) (f : V ⟶ U) :
    f.restriction.comp c.glueChartRestriction = d.glueChartRestriction := by
  apply BoundedAlgHom.ext
  intro b
  apply d.domainCover.algebra_ext_of_restrict_eq
  intro t
  have h := c.glueChartRestriction_test (d.domainCover.obj t) (d.domainCover.map t ≫ f)
    (d.index t) (d.left_subset t) (d.right_subset t) (d.domainCoverToChart t)
  exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
    (d.domainCover.obj t).algebra => q b)
    (h.trans (d.restriction_comp_glueChartRestriction t).symm)

end CompactIntersectionChartCover

theorem domainChartRestriction_test (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (W : Domain K (a.algebra i)) (p : W ⟶ U) (k : a.Index)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i))
    (hkj : Set.range (a.chart k) ⊆ Set.range (a.chart j))
    (g : W ⟶ a.restrictionDomain k i hki) :
    p.restriction.comp (a.domainChartRestriction i j U h) =
      g.restriction.comp (a.restriction k j hkj) :=
  (a.domainImageChartCover i j U h).glueChartRestriction_test W p k hki hkj g

theorem domainChartRestriction_naturality (i j : a.Index)
    {U V : Domain K (a.algebra i)} (f : V ⟶ U)
    (hU : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hV : a.chart i '' V.locus ⊆ Set.range (a.chart j)) :
    f.restriction.comp (a.domainChartRestriction i j U hU) =
      a.domainChartRestriction i j V hV :=
  (a.domainImageChartCover i j U hU).glueChartRestriction_naturality
    (a.domainImageChartCover i j V hV) f

/-- A single original common chart recovers the existing entire bounded
restriction, without any assumption that it contains the original source chart. -/
theorem domainChartRestriction_of_commonChart (i j k : a.Index)
    (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i))
    (hkj : Set.range (a.chart k) ⊆ Set.range (a.chart j))
    (f : U ⟶ a.restrictionDomain k i hki) :
    a.domainChartRestriction i j U h = f.restriction.comp (a.restriction k j hkj) :=
  a.domainChartRestriction_test i j U h U (𝟙 U) k hki hkj f

/-- If the first original chart is contained in the second, the constructed
map is the original chart restriction followed by U's original base map. -/
theorem domainChartRestriction_of_chartSubset (i j : a.Index)
    (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    a.domainChartRestriction i j U h = U.baseMap.comp (a.restriction i j hij) := by
  let f : U ⟶ a.restrictionDomain i i Subset.rfl :=
    ⟨U.baseMap, by
      change U.baseMap.comp (a.restriction i i Subset.rfl) = U.baseMap
      rw [a.restriction_id, BoundedAlgHom.comp_id]⟩
  exact a.domainChartRestriction_of_commonChart i j i U h Subset.rfl hij f

theorem domainChartRestriction_self (i : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart i)) :
    a.domainChartRestriction i i U h = U.baseMap := by
  rw [a.domainChartRestriction_of_chartSubset i i U h Subset.rfl,
    a.restriction_id, BoundedAlgHom.comp_id]

/-- Containing original target chart restrictions commute with the constructed map. -/
theorem domainChartRestriction_comp_original (i j k : a.Index)
    (U : Domain K (a.algebra i))
    (hj : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hk : a.chart i '' U.locus ⊆ Set.range (a.chart k))
    (hjk : Set.range (a.chart j) ⊆ Set.range (a.chart k)) :
    (a.domainChartRestriction i j U hj).comp (a.restriction j k hjk) =
      a.domainChartRestriction i k U hk := by
  let c := a.domainImageChartCover i j U hj
  apply BoundedAlgHom.ext
  intro b
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro t
  have h₁ := congrArg (fun q : BoundedAlgHom K (a.algebra j)
    (c.domainCover.obj t).algebra => q.comp (a.restriction j k hjk))
    (c.restriction_comp_glueChartRestriction t)
  have h₂ := congrArg (fun q : BoundedAlgHom K (a.algebra k)
    (a.algebra (c.index t)) => (c.domainCoverToChart t).restriction.comp q)
    (a.restriction_comp (c.index t) j k (c.right_subset t) hjk
      ((c.right_subset t).trans hjk)).symm
  have h₃ := a.domainChartRestriction_test i k U hk
    (c.domainCover.obj t) (c.domainCover.map t) (c.index t) (c.left_subset t)
    ((c.right_subset t).trans hjk) (c.domainCoverToChart t)
  exact congrArg (fun q : BoundedAlgHom K (a.algebra k)
    (c.domainCover.obj t).algebra => q b) ((h₁.trans h₂).trans h₃.symm)

end Langlands.Analytic.IndexedAffinoidAtlas
