import Langlands.Geometry.Analytic.StrongRefiningSourceSeparation
import Langlands.Geometry.Analytic.AtlasDomainRestrictionGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainIntersection

/-! # Bounded algebra-map descent along refining original subatlases -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {R : Type z} [NormedCommRing R] [NormedAlgebra K R]

/-- Compatible actual bounded maps to the unchanged algebras of selected
original charts. Only original containment equations are supplied. -/
structure SelectedBoundedMapFamily (a : IndexedAffinoidAtlas.{u, v, w} K X)
    (P : a.RefiningSelection) (R : Type z) [NormedCommRing R] [NormedAlgebra K R] where
  map : ∀ i, i ∈ P → BoundedAlgHom K R (a.algebra i)
  naturality : ∀ i j (hi : i ∈ P) (hj : j ∈ P)
    (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j)),
    (a.restriction i j hij).comp (map j hj) = map i hi

namespace SelectedBoundedMapFamily

variable {P : a.RefiningSelection} (d : SelectedBoundedMapFamily a P R)

/-- Original containment equations imply agreement on every actual common
full-domain test, by finite common-chart refinement and algebra separation. -/
theorem overlap (i k l : a.Index) (hk : k ∈ P) (hl : l ∈ P)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i))
    (hli : Set.range (a.chart l) ⊆ Set.range (a.chart i))
    (W : Domain K (a.algebra i))
    (f : W ⟶ a.restrictionDomain k i hki)
    (g : W ⟶ a.restrictionDomain l i hli) :
    f.restriction.comp (d.map k hk) = g.restriction.comp (d.map l hl) := by
  let c := a.compactIntersectionChartCover k l (a.chart i '' W.locus)
    (W.isCompact_locus.image (a.isEmbedding_chart i).continuous)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨f.subset hx, g.subset hx⟩)
  let e : a.CompactIntersectionChartCover i k (a.chart i '' W.locus) :=
    ⟨c.size, c.index, fun t => (c.left_subset t).trans hki,
      c.left_subset, c.covers⟩
  have hlocal (t : Fin e.size) :
      (e.domainCover.map t).restriction.comp f.restriction =
        (e.domainCoverToChart t).restriction.comp
          (a.restriction (e.index t) k (c.left_subset t)) := by
    apply a.restriction_hom_ext k i hki (e.domainCover.obj t).algebra
    erw [BoundedAlgHom.comp_assoc, f.comp_baseMap,
      BoundedAlgHom.comp_assoc,
      ← a.restriction_comp (e.index t) k i (c.left_subset t) hki (e.left_subset t)]
    exact (e.domainCover.map t).comp_baseMap.trans
      (e.domainCoverToChart t).comp_baseMap.symm
  have hlocal' (t : Fin e.size) :
      (e.domainCover.map t).restriction.comp g.restriction =
        (e.domainCoverToChart t).restriction.comp
          (a.restriction (e.index t) l (c.right_subset t)) := by
    apply a.restriction_hom_ext l i hli (e.domainCover.obj t).algebra
    erw [BoundedAlgHom.comp_assoc, g.comp_baseMap,
      BoundedAlgHom.comp_assoc,
      ← a.restriction_comp (e.index t) l i (c.right_subset t) hli (e.left_subset t)]
    exact (e.domainCover.map t).comp_baseMap.trans
      (e.domainCoverToChart t).comp_baseMap.symm
  apply BoundedAlgHom.ext
  intro r
  apply e.domainCover.algebra_ext_of_restrict_eq
  intro t
  have ht : e.index t ∈ P := P.downward_closed _ k (c.left_subset t) hk
  have heq :
      (e.domainCover.map t).restriction.comp (f.restriction.comp (d.map k hk)) =
        (e.domainCover.map t).restriction.comp (g.restriction.comp (d.map l hl)) := by
    erw [← BoundedAlgHom.comp_assoc, hlocal, BoundedAlgHom.comp_assoc,
      d.naturality _ _ ht hk, ← BoundedAlgHom.comp_assoc, hlocal',
      BoundedAlgHom.comp_assoc, d.naturality _ _ ht hl]
  exact congrArg (fun q : BoundedAlgHom K R (e.domainCover.obj t).algebra => q r) heq

/-- Every selected finite chart cover supplies a fully compatible bounded
family over the entire actual algebra of its parent chart. -/
theorem finiteCover_compatible {i : a.Index}
    (c : a.FiniteSelectedChartCover P.carrier i) :
    c.domainCover.BoundedMapCompatible (fun t => d.map (c.index t) (c.selected t)) := by
  intro t s W f g
  exact d.overlap i (c.index t) (c.index s) (c.selected t) (c.selected s)
    (c.subset t) (c.subset s) W f g

/-- Descend the finite compatible bounded family into the unchanged parent
algebra, including its original Banach norm. -/
def glueOnCover {i : a.Index} (c : a.FiniteSelectedChartCover P.carrier i) :
    BoundedAlgHom K R (a.algebra i) :=
  c.domainCover.glueBoundedAlgHom (fun t => d.map (c.index t) (c.selected t))
    (d.finiteCover_compatible c)

@[simp]
theorem restriction_comp_glueOnCover {i : a.Index}
    (c : a.FiniteSelectedChartCover P.carrier i) (t : Fin c.size) :
    (a.restriction (c.index t) i (c.subset t)).comp (d.glueOnCover c) =
      d.map (c.index t) (c.selected t) :=
  c.domainCover.restriction_comp_glueBoundedAlgHom _ _ t

/-- Recovery holds on every selected chart contained in the parent, not
only on the finitely many charts used to construct the glue. -/
theorem restriction_comp_glueOnCover_of_selected {i : a.Index}
    (c : a.FiniteSelectedChartCover P.carrier i) (k : a.Index) (hk : k ∈ P)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i)) :
    (a.restriction k i hki).comp (d.glueOnCover c) = d.map k hk := by
  let W := a.restrictionDomain k i hki
  let e : Domain.FiniteCover W :=
    { size := c.size
      obj t := W.inter (c.domainCover.obj t)
      map t := W.interLeft (c.domainCover.obj t)
      covers := by
        intro x hx
        obtain ⟨t, ht⟩ := c.domainCover.covers x (Set.mem_univ x)
        exact ⟨t, hx, ht⟩ }
  apply BoundedAlgHom.ext
  intro r
  apply e.algebra_ext_of_restrict_eq
  intro t
  have hleft : (e.map t).restriction.comp (a.restriction k i hki) =
      (W.interRight (c.domainCover.obj t)).restriction.comp
        (a.restriction (c.index t) i (c.subset t)) :=
    (e.map t).comp_baseMap.trans
      (W.interRight (c.domainCover.obj t)).comp_baseMap.symm
  have heq :
      (e.map t).restriction.comp
          ((a.restriction k i hki).comp (d.glueOnCover c)) =
        (e.map t).restriction.comp (d.map k hk) := by
    erw [← BoundedAlgHom.comp_assoc, hleft, BoundedAlgHom.comp_assoc,
      d.restriction_comp_glueOnCover c t]
    exact d.overlap i (c.index t) k (c.selected t) hk (c.subset t) hki
      (e.obj t) (W.interRight (c.domainCover.obj t)) (e.map t)
  exact congrArg (fun q : BoundedAlgHom K R (e.obj t).algebra => q r) heq

/-- Construct the bounded map on every original chart by compactness and
finite full-domain descent. No global map is input. -/
def extend (i : a.Index) : BoundedAlgHom K R (a.algebra i) :=
  d.glueOnCover (a.finiteSelectedChartCover P.carrier P.locally_refining i)

theorem restriction_comp_extend (i k : a.Index) (hk : k ∈ P)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i)) :
    (a.restriction k i hki).comp (d.extend i) = d.map k hk :=
  d.restriction_comp_glueOnCover_of_selected _ k hk hki

@[simp]
theorem extend_selected (i : a.Index) (hi : i ∈ P) :
    d.extend i = d.map i hi := by
  have h := d.restriction_comp_extend i i hi Subset.rfl
  rw [a.restriction_id, BoundedAlgHom.id_comp] at h
  exact h

/-- The constructed bounded maps satisfy every original source
restriction equation, with no selection or cover choices remaining. -/
theorem extend_naturality (i j : a.Index)
    (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    (a.restriction i j hij).comp (d.extend j) = d.extend i := by
  apply a.boundedAlgHom_ext_of_refiningSelection P.carrier P.locally_refining i
  intro k hk hki
  rw [← BoundedAlgHom.comp_assoc,
    ← a.restriction_comp k i j hki hij (hki.trans hij),
    d.restriction_comp_extend j k hk (hki.trans hij),
    d.restriction_comp_extend i k hk hki]

/-- Every bounded family on all original charts agreeing with the supplied
selected family is exactly the constructed extension. -/
theorem extend_unique (g : ∀ i, BoundedAlgHom K R (a.algebra i))
    (hg : ∀ i j (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j)),
      (a.restriction i j hij).comp (g j) = g i)
    (he : ∀ i (hi : i ∈ P), g i = d.map i hi) (i : a.Index) :
    g i = d.extend i := by
  apply a.boundedAlgHom_ext_of_refiningSelection P.carrier P.locally_refining i
  intro k hk hki
  rw [hg k i hki, he k hk, d.restriction_comp_extend i k hk hki]

end SelectedBoundedMapFamily
end Langlands.Analytic.IndexedAffinoidAtlas
