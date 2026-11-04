import Langlands.Geometry.Analytic.CompatibleStrongLocalization
import Langlands.Geometry.Analytic.SaturatedStrongLocalization
import Langlands.Geometry.Analytic.SaturatedComparisonEquivalence
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-! # Actual saturation comparison of the constructed localizations -/

noncomputable section

universe u v w

namespace Langlands.Analytic.CompatibleAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The actual saturation functor is a morphism of the two full
quasi-isomorphism classes. Original chart indices remain arbitrary. -/
def saturationLocalizer :
    LocalizerMorphism
      (quasiIsomorphisms (K := K) :
        MorphismProperty (CompatibleAtlasPresentation.{u, v, w} K))
      (SaturatedAtlasPresentation.quasiIsomorphisms (K := K)) where
  functor := saturationFunctor
  map _ _ f hf := (quasiIsomorphisms_saturationFunctor_map_iff f).mpr hf

/-- Descend the actual saturation functor to the two constructed quotients. -/
def localizedSaturationFunctor :
    LocalizedCategory.{u, v, w} (K := K) ⥤
      SaturatedAtlasPresentation.LocalizedCategory.{u, v, v} (K := K) :=
  descend (saturationFunctor ⋙ SaturatedAtlasPresentation.localizationFunctor)
    (saturationLocalizer.inverts SaturatedAtlasPresentation.localizationFunctor)

@[simp]
theorem localizationFunctor_localizedSaturationFunctor :
    (localizationFunctor (K := K)) ⋙ localizedSaturationFunctor =
      saturationFunctor ⋙ SaturatedAtlasPresentation.localizationFunctor :=
  localizationFunctor_descend _ _

/-- The quotient square commutes by the actual strict descent equation. -/
instance : CatCommSq (saturationLocalizer (K := K)).functor
    localizationFunctor SaturatedAtlasPresentation.localizationFunctor
    localizedSaturationFunctor :=
  CatCommSq.mk (eqToIso localizationFunctor_localizedSaturationFunctor).symm

@[simp]
theorem localizedSaturationFunctor_obj (A : CompatibleAtlasPresentation.{u, v, w} K) :
    localizedSaturationFunctor.obj (localizationFunctor.obj A) =
      SaturatedAtlasPresentation.localizationFunctor.obj (saturationFunctor.obj A) := rfl

@[simp]
theorem localizedSaturationFunctor_map {A B : CompatibleAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) :
    localizedSaturationFunctor.map (localizationFunctor.map f) =
      SaturatedAtlasPresentation.localizationFunctor.map (saturationFunctor.map f) :=
  Functor.congr_hom localizationFunctor_localizedSaturationFunctor f

/-- Every saturated full quasi-isomorphism is the saturation of an actual
original full quasi-isomorphism up to the constructed comparison isomorphisms. -/
theorem quasiIsomorphisms_le_map_saturationFunctor :
    (SaturatedAtlasPresentation.quasiIsomorphisms (K := K) :
      MorphismProperty (SaturatedAtlasPresentation.{u, v, v} K)) ≤
      (quasiIsomorphisms (K := K) :
        MorphismProperty (CompatibleAtlasPresentation.{u, v, v} K)).map saturationFunctor := by
  intro S T f hf
  let A : CompatibleAtlasPresentation.{u, v, v} K := ⟨S.presentation⟩
  let B : CompatibleAtlasPresentation.{u, v, v} K := ⟨T.presentation⟩
  let F : SaturatedAtlasPresentation.ofSaturation S.presentation ⟶
      SaturatedAtlasPresentation.ofSaturation T.presentation :=
    S.saturationIso.hom ≫ f ≫ T.saturationIso.inv
  have hF : F.IsQuasiIso := by
    exact (SaturatedAtlasPresentation.quasiIsomorphisms (K := K)).comp_mem _ _
      S.presentation.isQuasiIso_directFromSaturation
      ((SaturatedAtlasPresentation.quasiIsomorphisms (K := K)).comp_mem _ _
        hf T.presentation.isQuasiIso_directToSaturation)
  refine ⟨A, B, F.originalRestriction, hF.originalRestriction, ⟨?_⟩⟩
  refine Arrow.isoMk' _ f S.saturationIso T.saturationIso ?_
  change S.saturationIso.hom ≫ f =
    F.originalRestriction.saturationExtension ≫ T.saturationIso.hom
  rw [F.saturationExtension_originalRestriction]
  change S.saturationIso.hom ≫ f =
    (S.saturationIso.hom ≫ f ≫ T.saturationIso.inv) ≫ T.saturationIso.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

instance : (saturationLocalizer (K := K) :
    LocalizerMorphism
      (quasiIsomorphisms (K := K) :
        MorphismProperty (CompatibleAtlasPresentation.{u, v, v} K))
      (SaturatedAtlasPresentation.quasiIsomorphisms (K := K))).IsLocalizedEquivalence := by
  let : ((saturationLocalizer (K := K)).functor :
      CompatibleAtlasPresentation.{u, v, v} K ⥤ _).IsEquivalence :=
    inferInstanceAs ((saturationFunctor (K := K) :
      CompatibleAtlasPresentation.{u, v, v} K ⥤ _).IsEquivalence)
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  exact quasiIsomorphisms_le_map_saturationFunctor

instance : (localizedSaturationFunctor (K := K) :
    LocalizedCategory.{u, v, v} (K := K) ⥤ _).IsEquivalence :=
  (saturationLocalizer (K := K)).isEquivalence
    localizationFunctor SaturatedAtlasPresentation.localizationFunctor
    localizedSaturationFunctor

/-- The two actual localizations are equivalent when the original chart
indices lie in the ambient universe. The forward functor is the actual lift. -/
def localizedSaturationEquivalence :
    LocalizedCategory.{u, v, v} (K := K) ≌
      SaturatedAtlasPresentation.LocalizedCategory.{u, v, v} (K := K) :=
  (localizedSaturationFunctor (K := K)).asEquivalence

@[simp]
theorem localizedSaturationEquivalence_functor :
    (localizedSaturationEquivalence (K := K)).functor = localizedSaturationFunctor := rfl

/-- On the entire original quotient, actual saturation preserves the literal
descended ambient-space functor. This includes all paths and formal inverses. -/
theorem localizedSaturationFunctor_spaceFunctor :
    (localizedSaturationFunctor (K := K) :
      LocalizedCategory.{u, v, w} (K := K) ⥤ _) ⋙
        SaturatedAtlasPresentation.localizedSpaceFunctor = localizedSpaceFunctor := by
  apply localizedSpaceFunctor_unique
  calc
    (localizationFunctor : CompatibleAtlasPresentation.{u, v, w} K ⥤ _) ⋙
        (localizedSaturationFunctor ⋙ SaturatedAtlasPresentation.localizedSpaceFunctor) =
      (localizationFunctor ⋙ localizedSaturationFunctor) ⋙
        SaturatedAtlasPresentation.localizedSpaceFunctor := rfl
    _ = (saturationFunctor ⋙ SaturatedAtlasPresentation.localizationFunctor) ⋙
        SaturatedAtlasPresentation.localizedSpaceFunctor :=
      congrArg (fun G => G ⋙ SaturatedAtlasPresentation.localizedSpaceFunctor)
        localizationFunctor_localizedSaturationFunctor
    _ = saturationFunctor ⋙ (SaturatedAtlasPresentation.localizationFunctor ⋙
        SaturatedAtlasPresentation.localizedSpaceFunctor) := rfl
    _ = saturationFunctor ⋙ SaturatedAtlasPresentation.spaceFunctor :=
      congrArg (fun G => saturationFunctor ⋙ G)
        SaturatedAtlasPresentation.localizationFunctor_localizedSpaceFunctor
    _ = spaceFunctor := saturationFunctor_spaceFunctor

/-- The equivalence retains the original descended topological spaces and maps. -/
theorem localizedSaturationEquivalence_spaceFunctor :
    (localizedSaturationEquivalence (K := K)).functor ⋙
      SaturatedAtlasPresentation.localizedSpaceFunctor =
        (localizedSpaceFunctor : LocalizedCategory.{u, v, v} (K := K) ⥤ _) :=
  localizedSaturationFunctor_spaceFunctor

end Langlands.Analytic.CompatibleAtlasPresentation
