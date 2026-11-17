import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleAffineChartImages
import Langlands.AlgebraicGeometry.AlgebraicSpace.PointLiftedOpenCharts

/-! # Affine neighborhoods and gluing for structurally etale atlases -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleImages

/-- An affine target neighborhood and an affine source neighborhood above
one atlas point, with the actual sheaf pullback between them. -/
structure AffineAtlasNeighborhood {S : Scheme.{u}} (F : FppfSheaf S)
    {W Y : Over S} (a : (schemeYoneda S).obj W ⟶ F.obj)
    (f : F.obj ⟶ (schemeYoneda S).obj Y) (x : W.left) where
  base : Over S
  baseAffine : IsAffine base.left
  baseMap : base ⟶ Y
  baseOpen : _root_.AlgebraicGeometry.IsOpenImmersion baseMap.left
  sheaf : FppfSheaf S
  toSpace : sheaf.obj ⟶ F.obj
  toBase : sheaf.obj ⟶ (schemeYoneda S).obj base
  square : IsPullback toSpace toBase f ((schemeYoneda S).map baseMap)
  toSpaceOpen : IsOpenImmersion toSpace
  source : Over S
  sourceAffine : IsAffine source.left
  toAtlas : source ⟶ W
  atlasOpen : _root_.AlgebraicGeometry.IsOpenImmersion toAtlas.left
  composite : source ⟶ base
  compositeEtale : Etale composite.left
  chart : (schemeYoneda S).obj source ⟶ sheaf.obj
  chartEtale : IsEtale chart
  chart_toSpace : chart ≫ toSpace = (schemeYoneda S).map toAtlas ≫ a
  chart_toBase : chart ≫ toBase = (schemeYoneda S).map composite
  point : source.left
  point_eq : toAtlas.left point = x

/-- An etale scheme chart with etale composite admits affine source and
base neighborhoods at each source point. -/
theorem nonempty_affineAtlasNeighborhood
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (ha : IsEtale a)
    (f : F.obj ⟶ (schemeYoneda S).obj Y)
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    [Etale w.left] (x : W.left) :
    Nonempty (AffineAtlasNeighborhood F a f x) := by
  let i := Y.left.affineCover.idx (w.left x)
  obtain ⟨y, hy⟩ := Y.left.affineCover.covers (w.left x)
  let e₀ := Y.left.affineCover.f i
  let T : Over S := Over.mk (e₀ ≫ Y.hom)
  let e : T ⟶ Y := Over.homMk e₀
  let R : Over S := Over.mk (pullback.fst w.left e₀ ≫ W.hom)
  let p₁ : R ⟶ W := Over.homMk (pullback.fst w.left e₀)
  let p₂ : R ⟶ T := Over.homMk (pullback.snd w.left e₀) (by
    dsimp [R, T]
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w w])
  have hR : IsPullback p₁ p₂ w e := by
    apply IsPullback.of_map_of_faithful (F := Over.forget S)
    exact IsPullback.of_hasPullback w.left e₀
  obtain ⟨r, hr, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := w.left) (g := e₀) x y hy.symm
  let k := R.left.affineCover.idx r
  obtain ⟨z, hz⟩ := R.left.affineCover.covers r
  let l₀ := R.left.affineCover.f k
  let D : Over S := Over.mk (l₀ ≫ R.hom)
  let l : D ⟶ R := Over.homMk l₀
  let j := l ≫ p₁
  let q := l ≫ p₂
  let fS : F ⟶ (schemeSheaf S).obj Y := ObjectProperty.homMk f
  let G : FppfSheaf S := Limits.pullback fS ((schemeSheaf S).map e)
  let π : G.obj ⟶ F.obj := (pullback.fst fS ((schemeSheaf S).map e)).hom
  let p : G.obj ⟶ (schemeYoneda S).obj T :=
    (pullback.snd fS ((schemeSheaf S).map e)).hom
  have sq : IsPullback π p f ((schemeYoneda S).map e) :=
    (IsPullback.of_hasPullback fS ((schemeSheaf S).map e)).map
      (sheafToPresheaf (fppfTopology S) (Type (u + 1)))
  have hcomm : ((schemeYoneda S).map p₁ ≫ a) ≫ f =
      (schemeYoneda S).map p₂ ≫ (schemeYoneda S).map e := by
    rw [Category.assoc, hw, ← Functor.map_comp, ← Functor.map_comp, hR.w]
  let c : (schemeYoneda S).obj R ⟶ G.obj :=
    sq.lift ((schemeYoneda S).map p₁ ≫ a) ((schemeYoneda S).map p₂) hcomm
  have hbig : IsPullback ((schemeYoneda S).map p₁) (c ≫ p)
      (a ≫ f) ((schemeYoneda S).map e) := by
    rw [show c ≫ p = (schemeYoneda S).map p₂ from sq.lift_snd _ _ _, hw]
    exact hR.map (schemeYoneda S)
  have hc : IsPullback ((schemeYoneda S).map p₁) c a π :=
    hbig.of_bot (sq.lift_fst _ _ _).symm sq
  have hce : IsEtale c := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
        (schemeYoneda S)) hc ha
  have hπ : IsOpenImmersion π := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (SliceOpenGluing.openProperty S)
    exact MorphismProperty.of_isPullback
      (P := (SliceOpenGluing.openProperty S).relative (schemeYoneda S)) sq.flip
      (AffineOpenSubfunctors.isOpenImmersion_schemeYoneda_map e
        (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion e₀)))
  let b := (schemeYoneda S).map l ≫ c
  have hbe : IsEtale b := (isEtale_map l (by
    change Etale l₀
    infer_instance)).comp hce
  have hbπ : b ≫ π = (schemeYoneda S).map j ≫ a := by
    dsimp [b, c, j]
    rw [Category.assoc, sq.lift_fst, Functor.map_comp, Category.assoc]
  have hbp : b ≫ p = (schemeYoneda S).map q := by
    dsimp [b, c, q]
    rw [Category.assoc, sq.lift_snd, Functor.map_comp]
  have hq : Etale q.left := by
    change Etale (R.left.affineCover.f k ≫ pullback.snd w.left e₀)
    infer_instance
  refine ⟨{
    base := T
    baseAffine := inferInstanceAs (IsAffine (Y.left.affineCover.X i))
    baseMap := e
    baseOpen := inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion e₀)
    sheaf := G
    toSpace := π
    toBase := p
    square := sq
    toSpaceOpen := hπ
    source := D
    sourceAffine := inferInstanceAs (IsAffine (R.left.affineCover.X k))
    toAtlas := j
    atlasOpen := by
      change _root_.AlgebraicGeometry.IsOpenImmersion
        (R.left.affineCover.f k ≫ pullback.fst w.left e₀)
      infer_instance
    composite := q
    compositeEtale := hq
    chart := b
    chartEtale := hbe
    chart_toSpace := hbπ
    chart_toBase := hbp
    point := z
    point_eq := ?_ }⟩
  change (pullback.fst w.left e₀) (l₀ z) = x
  rw [hz]
  exact hr

/-- Compact local images of the affine neighborhoods give point lifts into
open scheme charts of the original sheaf. -/
theorem AffineAtlasNeighborhood.pointLift
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    {a : (schemeYoneda S).obj W ⟶ F.obj}
    {f : F.obj ⟶ (schemeYoneda S).obj Y} {x : W.left}
    (N : AffineAtlasNeighborhood F a f x)
    (hF : IsClosedImmersion (diag F.obj)) :
    ∃ (V D : Over S) (b : (schemeYoneda S).obj V ⟶ F.obj)
      (j : D ⟶ W) (c : D ⟶ V) (d : D.left),
      IsOpenImmersion b ∧
        (schemeYoneda S).map j ≫ a = (schemeYoneda S).map c ≫ b ∧
        j.left d = x := by
  let : IsAffine N.base.left := N.baseAffine
  let : IsAffine N.source.left := N.sourceAffine
  let : Etale N.composite.left := N.compositeEtale
  have hG : IsClosedImmersion (diag N.sheaf.obj) :=
    closed_diagonal_of_affine_pullback N.square hF
  obtain ⟨V, _, ⟨e⟩⟩ := of_affine_chart hG N.toBase N.chart N.chartEtale
    N.composite N.chart_toBase
  let Q := (Subfunctor.range N.chart).sheafify (fppfTopology S)
  have hQ : IsOpenImmersion Q.ι :=
    OpenSubfunctorImages.sheafify_range_open N.chart N.chartEtale
  let b := e.hom ≫ Q.ι ≫ N.toSpace
  let c : N.source ⟶ V := (schemeYoneda S).preimage
    (Subfunctor.toRangeSheafify (fppfTopology S) N.chart ≫ e.inv)
  have hc : (schemeYoneda S).map c ≫ b = N.chart ≫ N.toSpace := by
    dsimp [c, b]
    rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  exact ⟨V, N.source, b, N.toAtlas, c, N.point,
    (hQ.iso_comp e).comp' N.toSpaceOpen,
    N.chart_toSpace.symm.trans hc.symm, N.point_eq⟩

/-- A closed-diagonal fppf sheaf with a surjective etale scheme atlas and
an etale composite to a scheme is represented by an actual scheme. -/
theorem exists_representation_of_etale_composite
    {S : Scheme.{u}} (F : FppfSheaf S) {W Y : Over S}
    (hF : IsClosedImmersion (diag F.obj))
    (a : (schemeYoneda S).obj W ⟶ F.obj) (ha : IsEtale a) (hs : IsSurjective a)
    (f : F.obj ⟶ (schemeYoneda S).obj Y)
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    [Etale w.left] :
    ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅ F.obj) := by
  apply exists_representation_of_point_lifted_open_charts F a ha hs
  intro x
  obtain ⟨N⟩ := nonempty_affineAtlasNeighborhood a ha f w hw x
  exact N.pointLift hF

end Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleImages
