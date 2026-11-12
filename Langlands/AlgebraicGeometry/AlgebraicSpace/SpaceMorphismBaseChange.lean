import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenExtensionProduct

/-! # Morphism properties and the comparisons for scheme base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} (g : T ⟶ S)

/-- Restriction of presheaves commutes with their actual pullbacks. -/
def restrictPresheafPullbackIso {F G H : Presheaf S} (f : F ⟶ H) (h : G ⟶ H) :
    (restrictPresheaf g).obj (Limits.pullback f h) ≅
      Limits.pullback ((restrictPresheaf g).map f) ((restrictPresheaf g).map h) :=
  PreservesPullback.iso (restrictPresheaf g) f h

/-- The relative diagonal is carried to the relative diagonal by restriction. -/
theorem restrictPresheaf_map_pullback_diagonal {F G : Presheaf S} (f : F ⟶ G) :
    (restrictPresheaf g).map (pullback.diagonal f) ≫
        (restrictPresheafPullbackIso g f f).hom =
      pullback.diagonal ((restrictPresheaf g).map f) := by
  apply pullback.hom_ext
  · dsimp only [restrictPresheafPullbackIso]
    rw [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp,
      pullback.diagonal_fst, CategoryTheory.Functor.map_id, pullback.diagonal_fst]
  · dsimp only [restrictPresheafPullbackIso]
    rw [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp,
      pullback.diagonal_snd, CategoryTheory.Functor.map_id, pullback.diagonal_snd]

/-- Restriction preserves a relative scheme property of a relative diagonal. -/
theorem relative_pullback_diagonal_restrictPresheaf
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : Presheaf S} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
      (pullback.diagonal f)) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
      (pullback.diagonal ((restrictPresheaf g).map f)) := by
  rw [← restrictPresheaf_map_pullback_diagonal g f]
  exact MorphismProperty.RespectsIso.postcomp _ _ _
    (relative_restrictPresheaf_map P hf)

/-- The scheme-Yoneda base-change comparisons are natural in the represented scheme. -/
def schemeYonedaBaseChangeNatIso :
    Over.pullback g ⋙ schemeYoneda T ≅ schemeYoneda S ⋙ restrictPresheaf g :=
  NatIso.ofComponents (schemeYonedaBaseChangeIso g) (by
    intro U V φ
    ext Z a
    exact congrArg ULift.up
      ((Over.mapPullbackAdj g).homEquiv_naturality_right_symm a.down φ))

/-- Restricting a commutative chart square gives a commutative chart square. -/
theorem restrictAtlas_square {F G : Presheaf S} {U V : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (b : (schemeYoneda S).obj V ⟶ G)
    (φ : U ⟶ V) (f : F ⟶ G) (w : a ≫ f = (schemeYoneda S).map φ ≫ b) :
    restrictAtlas g a ≫ (restrictPresheaf g).map f =
      (schemeYoneda T).map ((Over.pullback g).map φ) ≫ restrictAtlas g b := by
  dsimp only [restrictAtlas]
  rw [Category.assoc, ← Functor.map_comp, w, Functor.map_comp]
  have hn := (schemeYonedaBaseChangeNatIso g).hom.naturality φ
  change (schemeYoneda T).map ((Over.pullback g).map φ) ≫
      (schemeYonedaBaseChangeIso g V).hom =
    (schemeYonedaBaseChangeIso g U).hom ≫
      (restrictPresheaf g).map ((schemeYoneda S).map φ) at hn
  rw [← Category.assoc, ← hn, Category.assoc]

/-- Scheme properties stable under base change are preserved on slice pullback maps. -/
theorem schemeProperty_overPullback_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {U V : Over S} (φ : U ⟶ V) (hφ : P φ.left) :
    P ((Over.pullback g).map φ).left := by
  have ho : IsPullback (pullback.fst U.hom g)
      (((Over.pullback g).map φ).left ≫ pullback.snd V.hom g)
      (φ.left ≫ V.hom) g := by
    simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w φ] using
      (IsPullback.of_hasPullback U.hom g)
  have hw : pullback.fst U.hom g ≫ φ.left =
      ((Over.pullback g).map φ).left ≫ pullback.fst V.hom g := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  exact MorphismProperty.of_isPullback
    (ho.of_bot hw (IsPullback.of_hasPullback V.hom g)) hφ

variable {g}

/-- A closed immersion of spaces stays a closed immersion after scheme base change. -/
theorem IsClosedImmersion.baseChangeMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsClosedImmersion (hom f)) :
    IsClosedImmersion (hom (baseChangeMap g f)) :=
  relative_restrictPresheaf_map @_root_.AlgebraicGeometry.IsClosedImmersion hf

/-- An open immersion of spaces stays an open immersion after scheme base change. -/
theorem IsOpenImmersion.baseChangeMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsOpenImmersion (hom f)) :
    IsOpenImmersion (hom (baseChangeMap g f)) :=
  relative_restrictPresheaf_map @_root_.AlgebraicGeometry.IsOpenImmersion hf

/-- A finite morphism of spaces stays finite after scheme base change. -/
theorem IsFinite.baseChangeMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsFinite (hom f)) : IsFinite (hom (baseChangeMap g f)) := by
  have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_restrictPresheaf_map @_root_.AlgebraicGeometry.IsFinite hf

/-- An affine morphism of spaces stays affine after scheme base change. -/
theorem IsAffineMorphism.baseChangeMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsAffineMorphism (hom f)) : IsAffineMorphism (hom (baseChangeMap g f)) := by
  have : MorphismProperty.RespectsIso (@IsAffineHom.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_restrictPresheaf_map @IsAffineHom hf

/-- A separated morphism of spaces stays separated after scheme base change. -/
theorem IsSeparatedMorphism.baseChangeMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsSeparatedMorphism f) : IsSeparatedMorphism (baseChangeMap g f) :=
  relative_pullback_diagonal_restrictPresheaf g @_root_.AlgebraicGeometry.IsClosedImmersion hf

/-- Local finite type of a morphism of spaces is preserved by scheme base change. -/
theorem IsLocallyOfFiniteTypeMorphism.baseChangeMap
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (hf : IsLocallyOfFiniteTypeMorphism f) :
    IsLocallyOfFiniteTypeMorphism (baseChangeMap g f) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩ := hf
  exact ⟨(Over.pullback g).obj U, (Over.pullback g).obj V,
    restrictAtlas g a, restrictAtlas g b, (Over.pullback g).map φ,
    relative_restrictAtlas _ ha, relative_restrictAtlas _ hs, relative_restrictAtlas _ hb,
    schemeProperty_overPullback_map g @LocallyOfFiniteType φ hφ,
    restrictAtlas_square g a b φ (hom f) hw⟩

/-- Smoothness of a morphism of spaces is preserved by scheme base change. -/
theorem IsSmoothMorphism.baseChangeMap
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (hf : IsSmoothMorphism f) :
    IsSmoothMorphism (baseChangeMap g f) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩ := hf
  exact ⟨(Over.pullback g).obj U, (Over.pullback g).obj V,
    restrictAtlas g a, restrictAtlas g b, (Over.pullback g).map φ,
    relative_restrictAtlas _ ha, relative_restrictAtlas _ hs, relative_restrictAtlas _ hb,
    schemeProperty_overPullback_map g @Smooth φ hφ,
    restrictAtlas_square g a b φ (hom f) hw⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
