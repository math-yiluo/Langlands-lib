import Langlands.Geometry.Analytic.RefiningBoundedMapDescent

/-! # Strong-map extension from refining source subatlases to greatest-chart targets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {P : A.atlas.RefiningSelection}
  (f : StrongHom (A.refiningSubpresentation P) B)
  (t : B.atlas.Index)
  (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t))

/-- The actual bounded pullbacks from a greatest target chart form a selected
bounded family on the original source, with only original restriction equations. -/
def selectedTopPullbacks :
    A.atlas.SelectedBoundedMapFamily P (B.atlas.algebra t) where
  map i hi := f.pullback ⟨i, hi⟩ t (f.image_chart_top t ht ⟨i, hi⟩)
  naturality i j hi hj hij := by
    have hc := f.restriction_comm ⟨i, hi⟩ ⟨j, hj⟩ t t hij Subset.rfl
        (f.image_chart_top t ht ⟨i, hi⟩) (f.image_chart_top t ht ⟨j, hj⟩)
    change (A.atlas.restriction i j hij).comp
        (f.pullback ⟨j, hj⟩ t (f.image_chart_top t ht ⟨j, hj⟩)) =
      (f.pullback ⟨i, hi⟩ t (f.image_chart_top t ht ⟨i, hi⟩)).comp
        (B.atlas.restriction t t Subset.rfl) at hc
    simpa only [B.atlas.restriction_id, BoundedAlgHom.comp_id] using hc

/-- The descended bounded map has precisely the unchanged continuous point
map, as proved by lifting every point to an actual selected covering chart. -/
theorem selectedTopPullbacks_extend_chart (i : A.atlas.Index)
    (x : BanachSpectrum (A.atlas.algebra i)) :
    B.atlas.chart t
        (BanachSpectrum.comap ((f.selectedTopPullbacks t ht).extend i).toBoundedRingHom x) =
      f.baseMap (A.atlas.chart i x) := by
  let c := A.atlas.finiteSelectedChartCover P.carrier P.locally_refining i
  obtain ⟨k, y, hy⟩ := c.covers (A.atlas.chart i x) ⟨x, rfl⟩
  have hxy : BanachSpectrum.comap
      (A.atlas.restriction (c.index k) i (c.subset k)).toBoundedRingHom y = x :=
    (A.atlas.isEmbedding_chart i).injective
      ((A.atlas.restriction_chart (c.index k) i (c.subset k) y).trans hy)
  have heq :
      BanachSpectrum.comap ((f.selectedTopPullbacks t ht).extend i).toBoundedRingHom
          (BanachSpectrum.comap
            (A.atlas.restriction (c.index k) i (c.subset k)).toBoundedRingHom y) =
        BanachSpectrum.comap
          (f.pullback ⟨c.index k, c.selected k⟩ t
            (f.image_chart_top t ht ⟨c.index k, c.selected k⟩)).toBoundedRingHom y := by
    apply BanachSpectrum.ext
    intro b
    exact congrArg (fun q : BoundedAlgHom K (B.atlas.algebra t)
      (A.atlas.algebra (c.index k)) => y (q b))
      ((f.selectedTopPullbacks t ht).restriction_comp_extend i
        (c.index k) (c.selected k) (c.subset k))
  conv_lhs => rw [← hxy, heq]
  exact (f.chart_comm ⟨c.index k, c.selected k⟩ t _ y).trans
    (congrArg f.baseMap hy)

/-- The constructed chosen map uses the greatest target chart and the
actual descended bounded maps into every unchanged original source algebra. -/
def extendTopChosen : A ⟶ B where
  baseMap := f.baseMap
  indexMap _ := t
  index_mono _ _ _ := Subset.rfl
  pullback := (f.selectedTopPullbacks t ht).extend
  chart_comm := f.selectedTopPullbacks_extend_chart t ht
  restriction_comm i j hij := by
    rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]
    exact (f.selectedTopPullbacks t ht).extend_naturality i j hij

/-- Extend to a full strong map using actual domain factorization for every
admissible target chart, without any source saturation premise. -/
def extendTop : StrongHom A B :=
  ofTopChart (f.extendTopChosen t ht) t ht

@[simp]
theorem extendTop_baseMap :
    (f.extendTop t ht).baseMap = f.baseMap := rfl

/-- Every original admissible bounded pullback on the selected source
subatlas is recovered, not just the pullback from the greatest target chart. -/
@[simp]
theorem extendTop_restrictSubatlasSource :
    (f.extendTop t ht).restrictSubatlasSource P.carrier P.locally_refining = f := by
  refine ext_of_pullback rfl ?_
  intro i j h h'
  apply B.atlas.restriction_hom_ext j t (ht j) (A.atlas.algebra i.val)
  have hext := ofTopChart_pullback_comp_restriction
    (f.extendTopChosen t ht) t ht i.val j h
  change ((f.extendTop t ht).pullback i.val j h).comp
      (B.atlas.restriction j t (ht j)) =
    (f.pullback i j h').comp (B.atlas.restriction j t (ht j))
  refine hext.trans ?_
  change ((f.selectedTopPullbacks t ht).extend i.val).comp
      (B.atlas.restriction t t (ht t)) =
    (f.pullback i j h').comp (B.atlas.restriction j t (ht j))
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]
  exact ((f.selectedTopPullbacks t ht).extend_selected i.val i.property).trans
    (f.pullback_comp_restriction i j t (ht j) h'
      (f.image_chart_top t ht i))

/-- Complete bounded-map source separation proves uniqueness among all
strong extensions with the prescribed original selected restriction. -/
theorem extendTop_unique (g : StrongHom A B)
    (hg : g.restrictSubatlasSource P.carrier P.locally_refining = f) :
    g = f.extendTop t ht := by
  apply restrictSubatlasSource_injective P.carrier P.locally_refining
  exact hg.trans (f.extendTop_restrictSubatlasSource t ht).symm

/-- Strong maps into a greatest-chart target are unchanged by any downward
closed locally refining original source selection, with explicit inverse. -/
def refiningSourceTopHomEquiv :
    StrongHom A B ≃ StrongHom (A.refiningSubpresentation P) B where
  toFun g := g.restrictSubatlasSource P.carrier P.locally_refining
  invFun g := g.extendTop t ht
  left_inv g := (g.restrictSubatlasSource P.carrier P.locally_refining).extendTop_unique
    t ht g rfl |>.symm
  right_inv g := g.extendTop_restrictSubatlasSource t ht

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
