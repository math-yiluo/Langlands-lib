import Langlands.Geometry.Analytic.GroundFieldExtensionQuasiIsoProof
import Mathlib.Topology.Category.TopCat.ULift

/-! # Ground field extension in the localized analytic category -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open CategoryTheory SaturatedAtlasPresentation
open IndexedAffinoidAtlas.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

private theorem saturatedLocalizedFunctor_inverts :
    (quasiIsomorphisms (K := K) :
      MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K)).IsInvertedBy
        (saturatedLocalizedFunctor K L) := by
  intro A B f hf
  let g := (SaturatedAtlasPresentation.compatibleFunctor (K := K)).map f
  let gL := compatibleMap K L g
  have hg : gL.toStrongHom.IsQuasiIso := groundFieldExtensionQuasiIso K L g hf
  exact Localization.inverts (localizationFunctor (K := L)) (quasiIsomorphisms (K := L)) _
    ((CompatibleAtlasPresentation.quasiIsomorphisms_saturationFunctor_map_iff gL).2 hg)

/-- Ground field extension on the localized category, induced by the actual scalar-extended
affinoid charts and bounded pullbacks. -/
def localizedFunctor :
    LocalizedCategory.{u, v, w} (K := K) ⥤
      LocalizedCategory.{u', max u' w, max u' w} (K := L) :=
  descend (saturatedLocalizedFunctor K L) (saturatedLocalizedFunctor_inverts K L)

@[simp]
theorem localizationFunctor_localizedFunctor :
    (localizationFunctor (K := K)) ⋙ localizedFunctor K L =
      saturatedLocalizedFunctor K L :=
  localizationFunctor_descend _ _

@[simp]
theorem localizedFunctor_map {A B : SaturatedAtlasPresentation.{u, v, w} K} (f : A ⟶ B) :
    (localizedFunctor K L).map (localizationFunctor.map f) =
      (saturatedLocalizedFunctor K L).map f :=
  Functor.congr_hom (localizationFunctor_localizedFunctor K L) f

private def saturatedProjection :
    saturatedLocalizedFunctor.{u, v, w, u'} K L ⋙ localizedSpaceFunctor ⋙
      TopCat.uliftFunctor.{v, max u' w} ⟶
    SaturatedAtlasPresentation.spaceFunctor ⋙ TopCat.uliftFunctor.{max u' w, v} where
  app A := TopCat.ofHom ⟨fun z => ULift.up (projection K L A.presentation.atlas z.down),
    continuous_uliftUp.comp ((continuous_projection K L A.presentation.atlas).comp
      continuous_uliftDown)⟩
  naturality A B f := by
    apply TopCat.hom_ext
    refine ContinuousMap.ext fun z => ?_
    change ULift.up (projection K L B.presentation.atlas
        (localizedSpaceFunctor.map ((saturatedLocalizedFunctor K L).map f) z.down)) =
      ULift.up (f.baseMap (projection K L A.presentation.atlas z.down))
    unfold saturatedLocalizedFunctor
    simp only [Functor.comp_map, localizedSpaceFunctor_map]
    exact congrArg ULift.up (projection_pointMap K L f
      ((SaturatedAtlasPresentation.compatibleFunctor (K := K)).map f).compatible z.down)

/-- The continuous projection from the scalar-extended space to the original space is natural
in localized analytic morphisms. The universe lifts allow the two spaces to have different
universes. -/
def localizedProjection :
    localizedFunctor.{u, v, w, u'} K L ⋙ localizedSpaceFunctor ⋙
      TopCat.uliftFunctor.{v, max u' w} ⟶
    localizedSpaceFunctor ⋙ TopCat.uliftFunctor.{max u' w, v} :=
  Localization.Construction.natTransExtension
    (eqToHom (congrArg
      (fun F => F ⋙ localizedSpaceFunctor ⋙ TopCat.uliftFunctor.{v, max u' w})
      (localizationFunctor_localizedFunctor K L)) ≫
      saturatedProjection K L ≫
      eqToHom (congrArg (fun F => F ⋙ TopCat.uliftFunctor.{max u' w, v})
        (localizationFunctor_localizedSpaceFunctor (K := K)).symm))

@[simp]
theorem localizedProjection_app (A : SaturatedAtlasPresentation.{u, v, w} K)
    (z : (chartSystem K L A.presentation.atlas).Space) :
    (localizedProjection K L).app (localizationFunctor.obj A) (ULift.up z) =
      ULift.up (projection K L A.presentation.atlas z) := rfl

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
