import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothMorphismCharts
import Langlands.Global.AdelicSpaceLevelPointsStatement

/-! # Properties of morphisms after composition of bases -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

variable {S T : Scheme.{u}} (g : S ⟶ T)

/-- Composed presheaves preserve the actual pullback, with its two projections. -/
def pullbackIso {F G H : Presheaf S} (f : F ⟶ H) (h : G ⟶ H) :
    presheaf g (Limits.pullback f h) ≅ Limits.pullback (map g f) (map g h) :=
  (map_isPullback g (IsPullback.of_hasPullback f h)).isoPullback

@[reassoc (attr := simp)]
theorem pullbackIso_hom_fst {F G H : Presheaf S} (f : F ⟶ H) (h : G ⟶ H) :
    (pullbackIso g f h).hom ≫ pullback.fst _ _ = map g (pullback.fst f h) :=
  (map_isPullback g (IsPullback.of_hasPullback f h)).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem pullbackIso_hom_snd {F G H : Presheaf S} (f : F ⟶ H) (h : G ⟶ H) :
    (pullbackIso g f h).hom ≫ pullback.snd _ _ = map g (pullback.snd f h) :=
  (map_isPullback g (IsPullback.of_hasPullback f h)).isoPullback_hom_snd

/-- The mapped relative diagonal is the relative diagonal after the pullback comparison. -/
theorem map_pullback_diagonal {F G : Presheaf S} (f : F ⟶ G) :
    map g (pullback.diagonal f) ≫ (pullbackIso g f f).hom =
      pullback.diagonal (map g f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackIso_hom_fst]
    exact ((presheafFunctor g).map_comp _ _).symm.trans
      ((congrArg (fun k => (presheafFunctor g).map k) (pullback.diagonal_fst f)).trans
        ((presheafFunctor g).map_id F)) |>.trans (pullback.diagonal_fst (map g f)).symm
  · rw [Category.assoc, pullbackIso_hom_snd]
    exact ((presheafFunctor g).map_comp _ _).symm.trans
      ((congrArg (fun k => (presheafFunctor g).map k) (pullback.diagonal_snd f)).trans
        ((presheafFunctor g).map_id F)) |>.trans (pullback.diagonal_snd (map g f)).symm

/-- Represented scheme properties of a relative diagonal survive composition of bases. -/
theorem relative_pullback_diagonal (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : Presheaf S} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
      (pullback.diagonal f)) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
      (pullback.diagonal (map g f)) := by
  rw [← map_pullback_diagonal g f]
  exact MorphismProperty.RespectsIso.postcomp _ _ _ (relative_map g P hf)

/-- Separated morphisms stay separated when their base is composed. -/
theorem separated_spaceMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsSeparatedMorphism f) : IsSeparatedMorphism (spaceMap g f) :=
  relative_pullback_diagonal g @_root_.AlgebraicGeometry.IsClosedImmersion hf

/-- The same chart square commutes after composition of bases. -/
theorem fromScheme_square {F G : Presheaf S} {U V : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (b : (schemeYoneda S).obj V ⟶ G)
    (φ : U ⟶ V) (f : F ⟶ G) (hw : a ≫ f = (schemeYoneda S).map φ ≫ b) :
    fromScheme g a ≫ map g f =
      (schemeYoneda T).map ((Over.map g).map φ) ≫ fromScheme g b := by
  calc
    fromScheme g a ≫ map g f = (schemeIso g U).hom ≫ map g (a ≫ f) :=
      (Category.assoc _ _ _).trans (congrArg (fun k => (schemeIso g U).hom ≫ k)
        ((presheafFunctor g).map_comp a f).symm)
    _ = (schemeIso g U).hom ≫
        (map g ((schemeYoneda S).map φ) ≫ map g b) :=
      congrArg (fun k => (schemeIso g U).hom ≫ k)
        ((congrArg (fun k => map g k) hw).trans
          ((presheafFunctor g).map_comp ((schemeYoneda S).map φ) b))
    _ = ((schemeIso g U).hom ≫ map g ((schemeYoneda S).map φ)) ≫ map g b :=
      (Category.assoc _ _ _).symm
    _ = ((schemeYoneda T).map ((Over.map g).map φ) ≫ (schemeIso g V).hom) ≫ map g b :=
      congrArg (fun k => k ≫ map g b) (schemeIso_naturality g φ)
    _ = (schemeYoneda T).map ((Over.map g).map φ) ≫ fromScheme g b :=
      Category.assoc _ _ _

/-- Local finite type of a space morphism is preserved by composition of bases. -/
theorem locallyOfFiniteType_spaceMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteTypeMorphism f) :
    IsLocallyOfFiniteTypeMorphism (spaceMap g f) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩ := hf
  exact ⟨(Over.map g).obj U, (Over.map g).obj V, fromScheme g a, fromScheme g b,
    (Over.map g).map φ, relative_fromScheme g _ ha, relative_fromScheme g _ hs,
    relative_fromScheme g _ hb, hφ, fromScheme_square g a b φ (hom f) hw⟩

/-- Smoothness of a space morphism is preserved by composition of bases. -/
theorem smooth_spaceMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsSmoothMorphism f) : IsSmoothMorphism (spaceMap g f) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩ := hf
  exact ⟨(Over.map g).obj U, (Over.map g).obj V, fromScheme g a, fromScheme g b,
    (Over.map g).map φ, relative_fromScheme g _ ha, relative_fromScheme g _ hs,
    relative_fromScheme g _ hb, hφ, fromScheme_square g a b φ (hom f) hw⟩

/-- An actual etale chart square over the composed base, with the same underlying scheme map. -/
def morphismChart {X Y : AlgebraicSpace S} {f : X ⟶ Y} (c : EtaleMorphismChart f) :
    EtaleMorphismChart (spaceMap g f) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨(Over.map g).obj c.source, (Over.map g).obj c.target,
    fromScheme g c.sourceMap, fromScheme g c.targetMap, (Over.map g).map c.schemeMap,
    relative_fromScheme g _ c.sourceEtale, relative_fromScheme g _ c.targetEtale,
    fromScheme_square g c.sourceMap c.targetMap c.schemeMap (hom f) c.comm⟩

/-- Source-atlas surjectivity is preserved on the composed chart square. -/
theorem morphismChart_sourceSurjective {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (c : EtaleMorphismChart f) (hc : IsSurjective c.sourceMap) :
    IsSurjective (morphismChart g c).sourceMap :=
  relative_fromScheme g _ hc

/-- Relative dimension of the chart map is unchanged by composition of bases. -/
theorem morphismChart_smoothOfRelativeDimension {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (c : EtaleMorphismChart f) (d : ℕ) (hc : SmoothOfRelativeDimension d c.schemeMap.left) :
    SmoothOfRelativeDimension d (morphismChart g c).schemeMap.left := hc

/-- Structural atlas properties stable under composition transport along a base map with that property. -/
theorem hasAtlasProperty_space (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
    {X : AlgebraicSpace S} (hX : HasAtlasProperty P X) (hg : P g) :
    HasAtlasProperty P (space g X) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  exact ⟨(Over.map g).obj U, fromScheme g a, relative_fromScheme g _ ha,
    relative_fromScheme g _ hs, P.comp_mem U.hom g hU hg⟩

/-- Finite type in the arithmetic atlas sense transports along a finite-type affine-base map. -/
theorem finiteTypeOverRing_space {C D : Type u} [CommRing C] [CommRing D]
    (g : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of D)) [LocallyOfFiniteType g] [QuasiCompact g]
    {X : AlgebraicSpace (Spec (CommRingCat.of C))} (hX : FiniteTypeOverRing C X) :
    FiniteTypeOverRing D (space g X) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, a, ha, hs, hft, hqc⟩ := hX
  let : LocallyOfFiniteType U.hom := hft
  let : QuasiCompact U.hom := hqc
  refine ⟨(Over.map g).obj U, fromScheme g a, relative_fromScheme g _ ha,
    relative_fromScheme g _ hs, ?_, ?_⟩
  · change LocallyOfFiniteType (U.hom ≫ g)
    infer_instance
  · change QuasiCompact (U.hom ≫ g)
    infer_instance

end Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition
