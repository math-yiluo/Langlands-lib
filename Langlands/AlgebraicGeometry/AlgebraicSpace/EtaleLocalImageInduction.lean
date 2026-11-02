import Langlands.AlgebraicGeometry.AlgebraicSpace.CompactLocalImage
import Langlands.AlgebraicGeometry.AlgebraicSpace.OffDiagonalImageChart

/-! # Finite-field-fibre induction for local chart images -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleLocalImageInduction

open EtaleImageSaturation CompactLocalImage

/-- The precise effective descent step used after representing the saturation. -/
def CompactImageDescent (S : Scheme.{u}) : Prop :=
  ∀ {B T V : Over S} [IsAffine B.left] [IsAffine T.left] [IsAffine V.left]
    (e : B ⟶ T) [Etale e.left] {F G : FppfSheaf S}
    {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
    {f : F.obj ⟶ (schemeYoneda S).obj T} [Mono f]
    (_sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj V ⟶ G.obj) (_haOpen : IsOpenImmersion a)
    (w : V ⟶ B) [LocallyOfFiniteType w.left]
    (_ha : a ≫ p = (schemeYoneda S).map w),
    HasCompactRepresentation
      (((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)).preimage π) →
    HasCompactRepresentation
      ((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S))

variable {S : Scheme.{u}}

/-- Induction on a finite field-fibre bound reduces chart-image representation
exactly to the indicated effective descent step. -/
theorem of_hasFieldFibreBound (descend : CompactImageDescent S) (n : ℕ) :
    ∀ {B T V : Over S} [IsAffine B.left] [IsAffine T.left] [IsAffine V.left]
      (e : B ⟶ T) [Etale e.left] {F G : FppfSheaf S}
      {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
      {f : F.obj ⟶ (schemeYoneda S).obj T} [Mono f]
      (_sq : IsPullback π p f ((schemeYoneda S).map e))
      (a : (schemeYoneda S).obj V ⟶ G.obj) (_haOpen : IsOpenImmersion a)
      (w : V ⟶ B) [LocallyOfFiniteType w.left]
      (_ha : a ≫ p = (schemeYoneda S).map w)
      (_hn : HasFieldFibreBound e.left n),
      HasCompactRepresentation
        ((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B T V _ _ _ e _ F G π p f _ sq a haOpen w _ ha hn
    by_cases hsmall : n ≤ 1
    · have hbound : HasFieldFibreBound e.left 1 := by
        intro K _ t
        exact ⟨(hn K t).1, (hn K t).2.trans hsmall⟩
      have heOpen := isOpenImmersion_of_hasFieldFibreBound_one e.left hbound
      have hπ : IsOpenImmersion π := by
        let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
          (SliceOpenGluing.openProperty S)
        exact MorphismProperty.of_isPullback
          (P := (SliceOpenGluing.openProperty S).relative (schemeYoneda S))
          sq.flip (AffineOpenSubfunctors.isOpenImmersion_schemeYoneda_map e heOpen)
      exact of_open_chart (a ≫ π) (haOpen.comp' hπ)
    · have hpos : 1 < n := by omega
      let e' : off e ⟶ B := offι e ≫ left e
      have : IsAffine (off e).left :=
        inferInstanceAs (IsAffine (EtaleOffDiagonal.scheme e.left))
      have : Etale e'.left :=
        inferInstanceAs (Etale (EtaleOffDiagonal.projection e.left))
      have hbound : HasFieldFibreBound e'.left (n - 1) := by
        apply EtaleOffDiagonal.hasFieldFibreBound e.left (n - 1)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hn
      obtain ⟨C⟩ := nonempty_offDiagonalImageChart e w sq a haOpen ha
      have : Mono p := sq.mono_snd_of_mono
      have : IsAffine (offChart e w).left := isAffine_offDiagonalChart e w
      have : LocallyOfFiniteType
          (pullback.fst (offι e ≫ right e) w).left :=
        locallyOfFiniteType_offDiagonalChart e w
      have hC := ih (n - 1) (by omega) e' C.square C.chart C.chartOpen
        (pullback.fst (offι e ≫ right e) w) C.chart_toBase hbound
      have hC' : HasCompactRepresentation
          ((Subfunctor.range ((schemeYoneda S).map (offChartι e w) ≫
            translate e w sq a ha)).sheafify (fppfTopology S)) := by
        rw [← C.chart_toSpace]
        exact hC
      have haEtale : IsEtale a :=
        MorphismProperty.relative_monotone (F := schemeYoneda S)
          (MorphismProperty.monotone_inverseImage (Over.forget S)
            (show (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) ≤ (@Etale.{u}) from
              fun _ _ _ _ => inferInstance)) a haOpen
      have hπEtale : IsEtale π := by
        let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
          (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
        exact MorphismProperty.of_isPullback
          (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
            (schemeYoneda S)) sq.flip (isEtale_map e inferInstance)
      have htranslate : IsEtale (translate e w sq a ha) := by
        let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
          (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
        exact MorphismProperty.of_isPullback
          (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
            (schemeYoneda S)) (translate_isPullback e w sq a ha)
              (haEtale.comp hπEtale)
      have hc : IsEtale ((schemeYoneda S).map (offChartι e w) ≫
          translate e w sq a ha) :=
        (isEtale_map (offChartι e w) inferInstance).comp htranslate
      have hR := of_union G.property a haOpen _ hc hC'
      rw [← saturation_eq e w sq a ha G.property] at hR
      exact descend e sq a haOpen w ha hR

/-- Every etale morphism between affine schemes has such a finite bound. -/
theorem of_affine_etale (descend : CompactImageDescent S)
    {B T V : Over S} [IsAffine B.left] [IsAffine T.left] [IsAffine V.left]
    (e : B ⟶ T) [Etale e.left] {F G : FppfSheaf S}
    {π : G.obj ⟶ F.obj} {p : G.obj ⟶ (schemeYoneda S).obj B}
    {f : F.obj ⟶ (schemeYoneda S).obj T} [Mono f]
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj V ⟶ G.obj) (haOpen : IsOpenImmersion a)
    (w : V ⟶ B) [LocallyOfFiniteType w.left]
    (ha : a ≫ p = (schemeYoneda S).map w) :
    HasCompactRepresentation
      ((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)) :=
  of_hasFieldFibreBound descend (affineEtalePointBound e.left) e sq a haOpen w ha
    (hasFieldFibreBound_affineEtalePointBound e.left)

end Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleLocalImageInduction
