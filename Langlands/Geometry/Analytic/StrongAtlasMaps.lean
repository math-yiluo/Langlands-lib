import Langlands.Geometry.Analytic.AtlasRestriction

/-! # All-admissible-pair bounded atlas maps and greatest target charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Strong-map data on actual supplied atlases: every admissible chart pair
has a bounded pullback, compatible with both atlas restrictions. -/
structure StrongHom (A B : AffinoidAtlasPresentation.{u, v, w} K) where
  baseMap : C(A.space, B.space)
  target_exists : ∀ i, ∃ j,
    baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)
  pullback : ∀ i j,
    baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) →
      BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i)
  chart_comm : ∀ i j h (x : BanachSpectrum (A.atlas.algebra i)),
    B.atlas.chart j (BanachSpectrum.comap (pullback i j h).toBoundedRingHom x) =
      baseMap (A.atlas.chart i x)
  restriction_comm : ∀ i i' j j'
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j')),
    (A.atlas.restriction i i' hi).comp (pullback i' j' h') =
      (pullback i j h).comp (B.atlas.restriction j j' hj)

namespace StrongHom

@[ext]
theorem ext {f g : StrongHom A B} (hb : f.baseMap = g.baseMap)
    (hp : HEq f.pullback g.pullback) : f = g := by
  cases f
  cases g
  cases hb
  cases eq_of_heq hp
  rfl

/-- Identity uses the actual atlas restriction for every admissible pair. -/
def id (A : AffinoidAtlasPresentation.{u, v, w} K) : StrongHom A A where
  baseMap := ContinuousMap.id A.space
  target_exists i := ⟨i, by simp⟩
  pullback i j h := A.atlas.restriction i j (by simpa using h)
  chart_comm i j h x := A.atlas.restriction_chart i j _ x
  restriction_comm i i' j j' hi hj h h' := by
    have hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j) := by
      simpa using h
    have hi'j' : Set.range (A.atlas.chart i') ⊆ Set.range (A.atlas.chart j') := by
      simpa using h'
    exact (A.atlas.restriction_comp i i' j' hi hi'j' (hi.trans hi'j')).symm.trans
      (A.atlas.restriction_comp i j j' hij hj (hi.trans hi'j'))

/-- Naturality for a fixed source chart is an equality of bounded maps. -/
theorem pullback_comp_restriction (f : StrongHom A B) (i : A.atlas.Index)
    (j j' : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j')) :
    f.pullback i j' h' = (f.pullback i j h).comp (B.atlas.restriction j j' hj) := by
  simpa only [A.atlas.restriction_id, BoundedAlgHom.id_comp] using
    f.restriction_comm i i j j' Subset.rfl hj h h'

/-- A greatest target chart contains the image of each source chart. -/
theorem image_chart_top (f : StrongHom A B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t))
    (i : A.atlas.Index) :
    f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart t) := by
  obtain ⟨j, hj⟩ := f.target_exists i
  exact hj.trans (ht j)

/-- Choose the greatest target chart, retaining its actual local pullbacks. -/
def toChosen (f : StrongHom A B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t)) : A ⟶ B where
  baseMap := f.baseMap
  indexMap _ := t
  index_mono _ _ _ := Subset.rfl
  pullback i := f.pullback i t (f.image_chart_top t ht i)
  chart_comm i x := f.chart_comm i t _ x
  restriction_comm i i' hi := by
    simpa only [B.atlas.restriction_id, BoundedAlgHom.comp_id] using
      f.restriction_comm i i' t t hi Subset.rfl
        (f.image_chart_top t ht i) (f.image_chart_top t ht i')

end StrongHom

namespace Hom

/-- Coarsen all selected target charts to a supplied greatest target chart. -/
def withTargetChart (f : A ⟶ B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t)) : A ⟶ B where
  baseMap := f.baseMap
  indexMap _ := t
  index_mono _ _ _ := Subset.rfl
  pullback i := (f.pullback i).comp (B.atlas.restriction (f.indexMap i) t (ht _))
  chart_comm i x := by
    change B.atlas.chart t
      (BanachSpectrum.comap (B.atlas.restriction (f.indexMap i) t (ht _)).toBoundedRingHom
        (BanachSpectrum.comap (f.pullback i).toBoundedRingHom x)) = _
    rw [B.atlas.restriction_chart, f.chart_comm]
  restriction_comm i i' hi := by
    rw [B.atlas.restriction_id, BoundedAlgHom.comp_id,
      ← BoundedAlgHom.comp_assoc, f.restriction_comm, BoundedAlgHom.comp_assoc,
      ← B.atlas.restriction_comp]

end Hom

namespace StrongHom

/-- Construct all admissible chart-pair pullbacks using domain factorization
through the greatest target chart. No gluing output is assumed. -/
def ofTopChart (f : A ⟶ B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t)) :
    StrongHom A B where
  baseMap := f.baseMap
  target_exists i := ⟨t, (f.withTargetChart t ht).image_chart_subset i⟩
  pullback i j h := (f.withTargetChart t ht).localPullback i j (ht j) h
  chart_comm i j h x := (f.withTargetChart t ht).localPullback_chart i j (ht j) h x
  restriction_comm i i' j j' hi hj h h' :=
    (f.withTargetChart t ht).localPullback_naturality i i' j j' hi hj
      (ht j) (ht j') h h'

theorem ofTopChart_pullback_comp_restriction (f : A ⟶ B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t))
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    ((ofTopChart f t ht).pullback i j h).comp (B.atlas.restriction j t (ht j)) =
      (f.pullback i).comp (B.atlas.restriction (f.indexMap i) t (ht _)) :=
  (f.withTargetChart t ht).localPullback_comp_restriction i j (ht j) h

/-- The construction recovers the original bounded pullback at its selected
target, including algebraic information not detected on spectrum points. -/
theorem ofTopChart_pullback_selected (f : A ⟶ B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t))
    (i : A.atlas.Index) :
    (ofTopChart f t ht).pullback i (f.indexMap i) (f.image_chart_subset i) =
      f.pullback i :=
  ((f.withTargetChart t ht).localPullback_unique i (f.indexMap i) (ht _)
    (f.image_chart_subset i) (f.pullback i) rfl).symm

/-- All admissible local maps are determined algebraically by the maps to
the greatest target chart. -/
theorem ofTopChart_toChosen (f : StrongHom A B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t)) :
    ofTopChart (f.toChosen t ht) t ht = f := by
  refine StrongHom.ext (f := ofTopChart (f.toChosen t ht) t ht) (g := f) rfl ?_
  apply heq_of_eq
  funext i j h
  change f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) at h
  apply B.atlas.restriction_hom_ext j t (ht j) (A.atlas.algebra i)
  refine (ofTopChart_pullback_comp_restriction (f.toChosen t ht) t ht i j h).trans ?_
  change (f.pullback i t (f.image_chart_top t ht i)).comp
    (B.atlas.restriction t t (ht t)) =
      (f.pullback i j h).comp (B.atlas.restriction j t (ht j))
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]
  exact f.pullback_comp_restriction i j t (ht j) h (f.image_chart_top t ht i)

end StrongHom

/-- A chart-domain presentation has the original chart as its greatest index. -/
def chartTopIndex (A : AffinoidAtlasPresentation.{u, v, w} K) (j : A.atlas.Index) :
    (A.chartPresentation j).atlas.Index :=
  ⟨j, Subset.rfl⟩

theorem chartTop_contains (A : AffinoidAtlasPresentation.{u, v, w} K)
    (j : A.atlas.Index) (c : (A.chartPresentation j).atlas.Index) :
    Set.range ((A.chartPresentation j).atlas.chart c) ⊆
      Set.range ((A.chartPresentation j).atlas.chart (A.chartTopIndex j)) :=
  A.atlas.containedChart_subset j c (A.chartTopIndex j) c.property

/-- Every chosen map into an actual chart-domain presentation yields all
admissible local bounded maps of a strong morphism. -/
def Hom.toChartStrongHom (j : B.atlas.Index) (f : A ⟶ B.chartPresentation j) :
    StrongHom A (B.chartPresentation j) :=
  StrongHom.ofTopChart f (B.chartTopIndex j) (B.chartTop_contains j)

end Langlands.Analytic.AffinoidAtlasPresentation
