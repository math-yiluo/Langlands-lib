import Langlands.Geometry.Analytic.LocalizedOpenRelationPresentation

/-! # The pieces are open analytic subspaces of the glued space -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation

open _root_.CategoryTheory Set Topology IndexedAffinoidAtlas PresentedAffinoidAlgebra
open AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {R : LocalizedOpenRelation K}

variable (R) in
/-- The image of a piece in the glued space. -/
abbrev pieceRange (m : R.M) : Set R.Space := range (R.ι m)

theorem isOpen_pieceRange (m : R.M) : IsOpen (R.pieceRange m) :=
  (isOpenEmbedding_ι m).isOpen_range

variable (R) in
/-- The image of a piece, as an open analytic domain of the glued space. -/
abbrev pieceDomain (m : R.M) : R.presentation.AnalyticDomain :=
  R.presentation.openDomain (R.pieceRange m) (isOpen_pieceRange m)

theorem image_subset_pieceRange (c : R.PieceChart) : c.image ⊆ R.pieceRange c.m :=
  image_subset_range _ _

/-- The chart of a chart image of the open image of a piece. -/
theorem subspaceChart_val {m : R.M}
    (c : (R.presentation.domain (R.pieceDomain m)).presentation.atlas.Index)
    (x : BanachSpectrum (ChartImage.rep c.1).alg) :
    ((R.presentation.domain (R.pieceDomain m)).presentation.atlas.chart c x).val =
      R.ι (ChartImage.rep c.1).m ((ChartImage.rep c.1).chart x) := rfl

theorem pieceChart_image_subset {m : R.M} (i : (R.atl m).Index)
    (c : (R.presentation.domain (R.pieceDomain m)).presentation.atlas.Index)
    (h : (fun z => (⟨R.ι m z, z, rfl⟩ : R.pieceRange m)) '' range ((R.atl m).chart i) ⊆
      range ((R.presentation.domain (R.pieceDomain m)).presentation.atlas.chart c)) :
    (⟨m, i⟩ : R.PieceChart).image ⊆ (ChartImage.rep c.1).image := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨x, hx⟩ := h ⟨z, hz, rfl⟩
  have hx' : R.ι (ChartImage.rep c.1).m ((ChartImage.rep c.1).chart x) = R.ι m z :=
    congrArg Subtype.val hx
  show R.ι m z ∈ _
  rw [← hx']
  exact ⟨_, ⟨x, rfl⟩, rfl⟩

theorem cmap_restriction (S : PresentedAffinoidAlgebra K) (m : R.M) (i i' : (R.atl m).Index)
    (h : range ((R.atl m).chart i) ⊆ range ((R.atl m).chart i'))
    (φ : BoundedAlgHom K ((R.atl m).algebra i) S) :
    R.cmap S ⟨m, i'⟩ (φ.comp ((R.atl m).restriction i i' h)) = R.cmap S ⟨m, i⟩ φ :=
  (congrArg localizationFunctor.map
    (SmallAffinoidSpectrum.chartMap_of_subset (B := presentationOf (R.Z m)) S i i' h φ)).symm

theorem rep_image_subset_of_range_subset
    {m : R.M} (c c' : (R.presentation.domain (R.pieceDomain m)).presentation.atlas.Index)
    (hc : range ((R.presentation.domain (R.pieceDomain m)).presentation.atlas.chart c) ⊆
      range ((R.presentation.domain (R.pieceDomain m)).presentation.atlas.chart c')) :
    (ChartImage.rep c.1).image ⊆ (ChartImage.rep c'.1).image := by
  have h := (atlas R).chart_subset_of_subspaceSubset (R.pieceRange m) c c' hc
  have h1 : range (chartMap c.1) ⊆ range (chartMap c'.1) := h
  rw [range_chartMap, range_chartMap] at h1
  rw [ChartImage.rep_image, ChartImage.rep_image]
  exact h1

variable (R) in
/-- The strong map from a piece onto its image in the glued space. -/
def pieceMap (m : R.M) : presentationOf (R.Z m) ⟶ R.presentation.domain (R.pieceDomain m) where
  baseMap := ⟨fun z => ⟨R.ι m z, z, rfl⟩, (continuous_ι m).subtype_mk _⟩
  target_exists i := by
    let T : R.ChartImage := ⟨(⟨m, i⟩ : R.PieceChart).image, ⟨m, i⟩, rfl⟩
    have hT : range (chartMap T) ⊆ R.pieceRange m := by
      rw [range_chartMap]; exact image_subset_pieceRange _
    refine ⟨⟨T, hT⟩, ?_⟩
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx : R.ι m ((R.atl m).chart i x) ∈ range (chartMap T) := by
      rw [range_chartMap]; exact ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  pullback i c h := rho ⟨m, i⟩ (ChartImage.rep c.1) (pieceChart_image_subset i c h)
  chart_comm i c h x := Subtype.ext (rho_chart ⟨m, i⟩ (ChartImage.rep c.1)
    (pieceChart_image_subset i c h) x)
  restriction_comm i i' c c' hi hc h h' := by
    have hsub : (⟨m, i⟩ : R.PieceChart).image ⊆ (ChartImage.rep c'.1).image :=
      (pieceChart_image_subset i c h).trans (rep_image_subset_of_range_subset c c' hc)
    have h2 := rho_comp ⟨m, i⟩ (ChartImage.rep c.1) (ChartImage.rep c'.1)
      (pieceChart_image_subset i c h) (rep_image_subset_of_range_subset c c' hc) hsub
    have e := cmap_rho ⟨m, i'⟩ (ChartImage.rep c'.1) (pieceChart_image_subset i' c' h')
      ((R.atl m).algebra i) ((R.atl m).restriction i i' hi)
    have hrest : R.cmap ((R.atl m).algebra i) ⟨m, i'⟩ ((R.atl m).restriction i i' hi) =
        incl ⟨m, i⟩ := by
      have := cmap_restriction ((R.atl m).algebra i) m i i' hi
        (BoundedAlgHom.id K ((R.atl m).algebra i))
      rwa [BoundedAlgHom.id_comp] at this
    rw [hrest] at e
    exact (rho_unique ⟨m, i⟩ (ChartImage.rep c'.1) hsub _ e).trans h2

theorem isQuasiIso_pieceMap (m : R.M) : (R.pieceMap m).IsQuasiIso := by
  refine ⟨?_, fun i c h => ⟨(R.pieceMap m).isClosed_chartImageLocus i c h,
    (R.pieceMap m).range_pullback i c h, fun S φ hφ => ?_⟩⟩
  · exact (isOpenEmbedding_ι (R := R) m).isEmbedding.toHomeomorph.isHomeomorph
  · refine rho_universal ⟨m, i⟩ (ChartImage.rep c.1) (pieceChart_image_subset i c h) S φ
      fun x => ?_
    obtain ⟨_, ⟨z, rfl⟩, e⟩ := hφ x
    have e' : R.ι m ((R.atl m).chart i z) =
        R.ι (ChartImage.rep c.1).m ((ChartImage.rep c.1).chart
          (BanachSpectrum.comap φ.toBoundedRingHom x)) := congrArg Subtype.val e
    exact ⟨_, ⟨z, rfl⟩, e'⟩

variable (R) in
/-- A piece is isomorphic to its open image in the glued space. -/
def pieceIso (m : R.M) :
    R.Z m ≅ localizationFunctor.obj (R.presentation.domain (R.pieceDomain m)) :=
  localizedQuasiIso (R.pieceMap m) (isQuasiIso_pieceMap m)

variable (R) in
/-- The morphism from a piece to the glued space. -/
def ιL (m : R.M) : R.Z m ⟶ R.glued :=
  (R.pieceIso m).hom ≫ R.presentation.localizedDomainInclusion (R.pieceDomain m)

theorem openImmersion_ιL (m : R.M) : openImmersion (R.ιL m) :=
  ⟨R.pieceRange m, isOpen_pieceRange m, R.pieceIso m, rfl⟩

theorem ιL_apply (m : R.M) (z : localizedSpaceFunctor.obj (R.Z m)) :
    localizedSpaceFunctor.map (R.ιL m) z = R.ι m z := by
  have h1 := R.presentation.localizedSpaceFunctor_map_localizedDomainInclusion (R.pieceDomain m)
    (localizedSpaceFunctor.map (R.pieceIso m).hom z)
  have h2 : localizedSpaceFunctor.map (R.pieceIso m).hom z = (R.pieceMap m).baseMap z :=
    lsf_map_apply (R.pieceMap m) z
  have h3 : localizedSpaceFunctor.map (R.ιL m) z =
      localizedSpaceFunctor.map (R.presentation.localizedDomainInclusion (R.pieceDomain m))
        (localizedSpaceFunctor.map (R.pieceIso m).hom z) := by
    rw [ιL, Functor.map_comp]; rfl
  rw [h3, h1, h2]
  rfl

end Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation
