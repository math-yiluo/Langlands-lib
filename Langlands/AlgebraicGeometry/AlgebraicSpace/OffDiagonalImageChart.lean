import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleImageSaturation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Open charts on the off-diagonal base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open EtaleImageSaturation

variable {S : Scheme.{u}} {B T V : Over S}
    (e : B ⟶ T) [IsSeparated e.left] (w : V ⟶ B)

/-- The off-diagonal base change, with the open chart used in the recursive step. -/
structure OffDiagonalImageChart {F G : FppfSheaf S}
    {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
    {f : F.obj ⟶ (schemeYoneda S).obj T}
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj V ⟶ G.obj)
    (ha : a ≫ p = (schemeYoneda S).map w) where
  pullbackSheaf : FppfSheaf S
  toSpace : pullbackSheaf.obj ⟶ G.obj
  toBase : pullbackSheaf.obj ⟶ (schemeYoneda S).obj (off e)
  square : IsPullback toSpace toBase p ((schemeYoneda S).map (offι e ≫ left e))
  chart : (schemeYoneda S).obj (offChart e w) ⟶ pullbackSheaf.obj
  chartOpen : IsOpenImmersion chart
  chart_toBase : chart ≫ toBase =
    (schemeYoneda S).map (pullback.fst (offι e ≫ right e) w)
  chart_toSpace : chart ≫ toSpace =
    (schemeYoneda S).map (offChartι e w) ≫ translate e w sq a ha

set_option backward.isDefEq.respectTransparency false in
/-- The off-diagonal restriction of a transported open chart is an open chart
on an actual fppf sheaf pullback. -/
theorem nonempty_offDiagonalImageChart {F G : FppfSheaf S}
    {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
    {f : F.obj ⟶ (schemeYoneda S).obj T}
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj V ⟶ G.obj) (haOpen : IsOpenImmersion a)
    (ha : a ≫ p = (schemeYoneda S).map w) :
    Nonempty (OffDiagonalImageChart e w sq a ha) := by
  let l : off e ⟶ B := offι e ≫ left e
  let r : off e ⟶ B := offι e ≫ right e
  have hlr : l ≫ e = r ≫ e := by
    dsimp [l, r]
    rw [Category.assoc, (relation_isPullback e).w, ← Category.assoc]
  let pS : G ⟶ (schemeSheaf S).obj B := ObjectProperty.homMk p
  let H : FppfSheaf S := Limits.pullback pS ((schemeSheaf S).map l)
  let π' : H.obj ⟶ G.obj := (pullback.fst pS ((schemeSheaf S).map l)).hom
  let p' : H.obj ⟶ (schemeYoneda S).obj (off e) :=
    (pullback.snd pS ((schemeSheaf S).map l)).hom
  have sq' : IsPullback π' p' p ((schemeYoneda S).map l) :=
    (IsPullback.of_hasPullback pS ((schemeSheaf S).map l)).map
      (sheafToPresheaf (fppfTopology S) (Type (u + 1)))
  have hcompat : (π' ≫ π) ≫ f =
      (p' ≫ (schemeYoneda S).map r) ≫ (schemeYoneda S).map e := by
    rw [Category.assoc, sq.w, ← Category.assoc, sq'.w, Category.assoc,
      ← Functor.map_comp, hlr, Functor.map_comp, Category.assoc]
  let τ : H.obj ⟶ G.obj :=
    sq.lift (π' ≫ π) (p' ≫ (schemeYoneda S).map r) hcompat
  have hτπ : τ ≫ π = π' ≫ π := sq.lift_fst _ _ _
  have hτp : τ ≫ p = p' ≫ (schemeYoneda S).map r := sq.lift_snd _ _ _
  have sqτ : IsPullback τ p' p ((schemeYoneda S).map r) := by
    have houter : IsPullback (τ ≫ π) p' f
        ((schemeYoneda S).map r ≫ (schemeYoneda S).map e) := by
      rw [hτπ, ← Functor.map_comp, ← hlr, Functor.map_comp]
      exact sq'.paste_horiz sq
    exact houter.of_right hτp sq
  let c : (schemeYoneda S).obj (offChart e w) ⟶ G.obj :=
    (schemeYoneda S).map (offChartι e w) ≫ translate e w sq a ha
  let q : offChart e w ⟶ off e := pullback.fst r w
  let d : offChart e w ⟶ V := pullback.snd r w
  have hcp : c ≫ p = (schemeYoneda S).map q ≫ (schemeYoneda S).map l := by
    dsimp [c]
    rw [Category.assoc, translate_p, ← Functor.map_comp, ← Functor.map_comp]
    apply congrArg ((schemeYoneda S).map)
    dsimp [newBase, q, l, r]
    rw [← Category.assoc, offChartι_fst, Category.assoc]
  let b : (schemeYoneda S).obj (offChart e w) ⟶ H.obj :=
    sq'.lift c ((schemeYoneda S).map q) hcp
  have hbπ : b ≫ π' = c := sq'.lift_fst _ _ _
  have hbp : b ≫ p' = (schemeYoneda S).map q := sq'.lift_snd _ _ _
  have hbτ : b ≫ τ = (schemeYoneda S).map d ≫ a := by
    apply sq.hom_ext
    · rw [Category.assoc, hτπ, ← Category.assoc, hbπ]
      dsimp [c, d]
      rw [Category.assoc, translate_π, ← Functor.map_comp_assoc, offChartι_snd,
        Category.assoc]
    · rw [Category.assoc, hτp, ← Category.assoc, hbp, Category.assoc, ha,
        ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg ((schemeYoneda S).map) (pullback.condition (f := r) (g := w))
  have hchart : IsPullback ((schemeYoneda S).map d) b a τ := by
    have houter : IsPullback ((schemeYoneda S).map d) (b ≫ p')
        (a ≫ p) ((schemeYoneda S).map r) := by
      rw [hbp, ha]
      exact (IsPullback.of_hasPullback r w).flip.map (schemeYoneda S)
    exact houter.of_bot hbτ.symm sqτ
  have hbOpen : IsOpenImmersion b := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
        (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (Over.forget S)).relative
          (schemeYoneda S)) hchart haOpen
  exact ⟨{
    pullbackSheaf := H
    toSpace := π'
    toBase := p'
    square := sq'
    chart := b
    chartOpen := hbOpen
    chart_toBase := hbp
    chart_toSpace := hbπ }⟩

set_option backward.isDefEq.respectTransparency false in
/-- Affine endpoints make the fixed off-diagonal chart source affine. -/
theorem isAffine_offDiagonalChart [Etale e.left]
    [IsAffine B.left] [IsAffine T.left] [IsAffine V.left] :
    IsAffine (offChart e w).left := by
  let : IsAffine ((Over.forget S).obj (off e)) :=
    inferInstanceAs (IsAffine (EtaleOffDiagonal.scheme e.left))
  let : IsAffineHom ((Over.forget S).map w) := inferInstanceAs (IsAffineHom w.left)
  exact IsAffine.of_isPullback
    ((IsPullback.of_hasPullback (offι e ≫ right e) w).map (Over.forget S))

/-- The new chart map is the base change of the original locally finite type map. -/
theorem locallyOfFiniteType_offDiagonalChart [LocallyOfFiniteType w.left] :
    LocallyOfFiniteType (pullback.fst (offι e ≫ right e) w).left :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType.{u})
    ((IsPullback.of_hasPullback (offι e ≫ right e) w).map (Over.forget S)).flip
    (inferInstanceAs (LocallyOfFiniteType w.left))

end Langlands.AlgebraicGeometry.AlgebraicSpace
