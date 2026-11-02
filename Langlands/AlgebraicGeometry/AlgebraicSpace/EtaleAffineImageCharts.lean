import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleLocalFiniteCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleFiniteChartQuotient

/-! # Affine open image charts after an etale base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An affine etale base change on which a finite chart of an atlas has
affine open image, retaining a point above the original atlas point. -/
structure EtaleAffineImageChart {S : Scheme.{u}} (F : FppfSheaf S)
    {W Y : Over S} (a : (schemeYoneda S).obj W ⟶ F.obj)
    (f : F.obj ⟶ (schemeYoneda S).obj Y) (x : W.left) where
  base : Over S
  baseAffine : IsAffine base.left
  baseMap : base ⟶ Y
  baseEtale : Etale baseMap.left
  pullbackSheaf : FppfSheaf S
  toSpace : pullbackSheaf.obj ⟶ F.obj
  toBase : pullbackSheaf.obj ⟶ (schemeYoneda S).obj base
  square : IsPullback toSpace toBase f ((schemeYoneda S).map baseMap)
  source : Over S
  sourceAffine : IsAffine source.left
  toAtlas : source ⟶ W
  atlasEtale : Etale toAtlas.left
  finiteMap : source ⟶ base
  finite : _root_.AlgebraicGeometry.IsFinite finiteMap.left
  chart : (schemeYoneda S).obj source ⟶ pullbackSheaf.obj
  chartEtale : IsEtale chart
  chart_toSpace : chart ≫ toSpace = (schemeYoneda S).map toAtlas ≫ a
  chart_toBase : chart ≫ toBase = (schemeYoneda S).map finiteMap
  imageAffine : AffineOpenSubfunctors.IsAffineOpen
    ((Subfunctor.range chart).sheafify (fppfTopology S))
  point : source.left
  point_eq : toAtlas.left point = x

/-- Every finite chart of the atlas composite gives an affine open image
chart on the corresponding etale base change of the sheaf. -/
theorem nonempty_etaleAffineImageChart_of_finiteChart
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (ha : IsEtale a)
    (f : F.obj ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    (x : W.left) (C : EtaleFiniteChart w.left x) :
    Nonempty (EtaleAffineImageChart F a f x) := by
  let T : Over S := Over.mk (C.toBase ≫ Y.hom)
  let e : T ⟶ Y := Over.homMk C.toBase
  let D : Over S := Over.mk (C.toSource ≫ W.hom)
  let j : D ⟶ W := Over.homMk C.toSource
  let q : D ⟶ T := Over.homMk C.finiteMap (by
    dsimp [T, D]
    rw [← Category.assoc, ← C.comm, Category.assoc, Over.w w])
  let R : Over S :=
    Over.mk (pullback.fst w.left C.toBase ≫ W.hom)
  let p1 : R ⟶ W := Over.homMk (pullback.fst w.left C.toBase)
  let p2 : R ⟶ T := Over.homMk (pullback.snd w.left C.toBase) (by
    dsimp [R, T]
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w w])
  let r : D ⟶ R := Over.homMk
    (pullback.lift C.toSource C.finiteMap C.comm) (by
      dsimp [R, D]
      exact pullback.lift_fst_assoc _ _ _ _)
  have hR : IsPullback p1 p2 w e := by
    apply IsPullback.of_map_of_faithful (F := Over.forget S)
    exact IsPullback.of_hasPullback w.left C.toBase
  let fS : F ⟶ (schemeSheaf S).obj Y := ObjectProperty.homMk f
  let G : FppfSheaf S := Limits.pullback fS ((schemeSheaf S).map e)
  let π : G.obj ⟶ F.obj := (pullback.fst fS ((schemeSheaf S).map e)).hom
  let p : G.obj ⟶ (schemeYoneda S).obj T :=
    (pullback.snd fS ((schemeSheaf S).map e)).hom
  have sq : IsPullback π p f ((schemeYoneda S).map e) :=
    (IsPullback.of_hasPullback fS ((schemeSheaf S).map e)).map
      (sheafToPresheaf (fppfTopology S) (Type (u + 1)))
  have hcomm : ((schemeYoneda S).map p1 ≫ a) ≫ f =
      (schemeYoneda S).map p2 ≫ (schemeYoneda S).map e := by
    rw [Category.assoc, hw, ← Functor.map_comp, ← Functor.map_comp, hR.w]
  let c : (schemeYoneda S).obj R ⟶ G.obj :=
    sq.lift ((schemeYoneda S).map p1 ≫ a) ((schemeYoneda S).map p2) hcomm
  have hbig : IsPullback ((schemeYoneda S).map p1) (c ≫ p)
      (a ≫ f) ((schemeYoneda S).map e) := by
    rw [show c ≫ p = (schemeYoneda S).map p2 from sq.lift_snd _ _ _, hw]
    exact hR.map (schemeYoneda S)
  have hc : IsPullback ((schemeYoneda S).map p1) c a π :=
    hbig.of_bot (sq.lift_fst _ _ _).symm sq
  have hce : IsEtale c := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
        (schemeYoneda S)) hc ha
  let b := (schemeYoneda S).map r ≫ c
  have hbe : IsEtale b := (isEtale_map r C.etale_lift).comp hce
  have hr1 : r ≫ p1 = j := by ext; exact pullback.lift_fst _ _ _
  have hr2 : r ≫ p2 = q := by ext; exact pullback.lift_snd _ _ _
  have hbπ : b ≫ π = (schemeYoneda S).map j ≫ a := by
    dsimp [b, c]
    rw [Category.assoc, sq.lift_fst, ← Functor.map_comp_assoc, hr1]
  have hbp : b ≫ p = (schemeYoneda S).map q := by
    dsimp [b, c]
    rw [Category.assoc, sq.lift_snd, ← Functor.map_comp, hr2]
  let : Mono p := sq.mono_snd_of_mono
  let : IsAffine D.left := C.sourceAffine
  let : _root_.AlgebraicGeometry.IsFinite q.left := C.finite
  refine ⟨{
    base := T
    baseAffine := C.baseAffine
    baseMap := e
    baseEtale := C.baseEtale
    pullbackSheaf := G
    toSpace := π
    toBase := p
    square := sq
    source := D
    sourceAffine := C.sourceAffine
    toAtlas := j
    atlasEtale := C.sourceEtale
    finiteMap := q
    finite := C.finite
    chart := b
    chartEtale := hbe
    chart_toSpace := hbπ
    chart_toBase := hbp
    imageAffine :=
      isAffineOpen_sheafify_range_of_finite_mono_composite b hbe G.property p q hbp
    point := C.point
    point_eq := C.point_eq }⟩

/-- A separated locally finite type atlas composite that is quasi-finite
at `x` admits an affine open image chart above `x` after etale base change. -/
theorem nonempty_etaleAffineImageChart
    {S : Scheme.{u}} {F : FppfSheaf S} {W Y : Over S}
    (a : (schemeYoneda S).obj W ⟶ F.obj) (ha : IsEtale a)
    (f : F.obj ⟶ (schemeYoneda S).obj Y) [Mono f]
    (w : W ⟶ Y) (hw : a ≫ f = (schemeYoneda S).map w)
    [LocallyOfFiniteType w.left] [IsSeparated w.left]
    (x : W.left) (hx : w.left.QuasiFiniteAt x) :
    Nonempty (EtaleAffineImageChart F a f x) := by
  obtain ⟨C⟩ := nonempty_etaleFiniteChart w.left x hx
  exact nonempty_etaleAffineImageChart_of_finiteChart a ha f w hw x C

end Langlands.AlgebraicGeometry.AlgebraicSpace
