import Langlands.AlgebraicGeometry.AlgebraicSpace.MonomorphismAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleAffineImageCharts

/-! # Affine neighborhoods of an atlas over a scheme monomorphism -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

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
  toBaseMono : Mono toBase
  source : Over S
  sourceAffine : IsAffine source.left
  toAtlas : source ⟶ W
  atlasOpen : _root_.AlgebraicGeometry.IsOpenImmersion toAtlas.left
  composite : source ⟶ base
  compositeLft : LocallyOfFiniteType composite.left
  compositeLqf : LocallyQuasiFinite composite.left
  chart : (schemeYoneda S).obj source ⟶ sheaf.obj
  chartEtale : IsEtale chart
  chart_toSpace : chart ≫ toSpace = (schemeYoneda S).map toAtlas ≫ a
  chart_toBase : chart ≫ toBase = (schemeYoneda S).map composite
  point : source.left
  point_eq : toAtlas.left point = x

/-- Arbitrary atlases with a locally finite type composite over a
monomorphism admit these affine neighborhoods at every point. -/
theorem nonempty_affineAtlasNeighborhood
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (ha : IsEtale a)
    (f : F.obj ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    [LocallyOfFiniteType w.left] (x : W.left) :
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
  let : Mono p := sq.mono_snd_of_mono
  have hq : LocallyOfFiniteType q.left := by
    change LocallyOfFiniteType (R.left.affineCover.f k ≫ pullback.snd w.left e₀)
    infer_instance
  let : LocallyOfFiniteType q.left := hq
  have hqf : LocallyQuasiFinite q.left :=
    locallyQuasiFinite_of_etale_mono_composite b hbe p q hbp
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
    toBaseMono := inferInstance
    source := D
    sourceAffine := inferInstanceAs (IsAffine (R.left.affineCover.X k))
    toAtlas := j
    atlasOpen := by
      change _root_.AlgebraicGeometry.IsOpenImmersion
        (R.left.affineCover.f k ≫ pullback.fst w.left e₀)
      infer_instance
    composite := q
    compositeLft := hq
    compositeLqf := hqf
    chart := b
    chartEtale := hbe
    chart_toSpace := hbπ
    chart_toBase := hbp
    point := z
    point_eq := ?_ }⟩
  change (pullback.fst w.left e₀) (l₀ z) = x
  rw [hz]
  exact hr

/-- The local affine neighborhood has the separated finite-image chart
required by the subsequent etale image descent step. -/
theorem AffineAtlasNeighborhood.nonempty_etaleAffineImageChart
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    {a : (schemeYoneda S).obj W ⟶ F.obj}
    {f : F.obj ⟶ (schemeYoneda S).obj Y} {x : W.left}
    (N : AffineAtlasNeighborhood F a f x) :
    Nonempty (EtaleAffineImageChart N.sheaf N.chart N.toBase N.point) := by
  let : IsAffine N.source.left := N.sourceAffine
  let : LocallyOfFiniteType N.composite.left := N.compositeLft
  let : LocallyQuasiFinite N.composite.left := N.compositeLqf
  let : Mono N.toBase := N.toBaseMono
  exact _root_.Langlands.AlgebraicGeometry.AlgebraicSpace.nonempty_etaleAffineImageChart
    N.chart N.chartEtale N.toBase
    N.composite N.chart_toBase N.point (N.composite.left.quasiFiniteAt N.point)

end Langlands.AlgebraicGeometry.AlgebraicSpace
