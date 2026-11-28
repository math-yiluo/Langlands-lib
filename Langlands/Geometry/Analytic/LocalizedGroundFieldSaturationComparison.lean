import Langlands.Geometry.Analytic.CompatibleLocalizedGroundFieldExtension
import Langlands.Geometry.Analytic.LocalizedGroundFieldExtension
import Langlands.Geometry.Analytic.LocalizedSaturationEquivalence
import Langlands.Geometry.Analytic.SaturatedEtaleComparison

/-! # Comparison of scalar extension across saturation -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory

private def saturationForgetIso
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    (CompatibleAtlasPresentation.saturationFunctor ⋙ SaturatedAtlasPresentation.compatibleFunctor) ≅
      𝟭 (CompatibleAtlasPresentation.{u, v, v} K) := by
  let S : CompatibleAtlasPresentation.{u, v, v} K ⥤ SaturatedAtlasPresentation.{u, v, v} K :=
    CompatibleAtlasPresentation.saturationFunctor
  let I : SaturatedAtlasPresentation.{u, v, v} K ⥤ CompatibleAtlasPresentation.{u, v, v} K :=
    SaturatedAtlasPresentation.compatibleFunctor
  let ε : I ⋙ S ≅ 𝟭 _ := SaturatedAtlasPresentation.saturationComparisonNatIso
  change S ⋙ I ≅ 𝟭 _
  refine NatIso.ofComponents (fun A => S.preimageIso (ε.app (S.obj A))) ?_
  intro A B f
  apply S.map_injective
  change S.map (I.map (S.map f) ≫ S.preimage (ε.hom.app (S.obj B))) =
    S.map (S.preimage (ε.hom.app (S.obj A)) ≫ f)
  simpa only [Functor.map_comp, Functor.map_preimage, Functor.comp_map, Functor.id_map]
    using ε.hom.naturality (S.map f)

namespace CompleteUltrametricField

open AffinoidAtlasPresentation.GroundFieldExtension
open AffinoidAtlasPresentation.GroundFieldExtension.CompleteField

variable {K L : CompleteUltrametricField.{u}}

/-- The two scalar-extension functors agree up to the actual saturation comparison
on localized compatible atlases. The normed algebra is induced by the field embedding. -/
def localizedSaturationExtendIso (e : K ⟶ L) :
    letI := e.normedAlgebra
    (CompatibleAtlasPresentation.localizedSaturationFunctor :
      K.CompatibleAnalyticCategory.{u, v} ⥤ _) ⋙ localizedFunctor K L ≅
      localizedExtend e ⋙ CompatibleAtlasPresentation.localizedSaturationFunctor := by
  letI := e.normedAlgebra
  let Q : K.CompatibleCategory.{u, v} ⥤ K.CompatibleAnalyticCategory.{u, v} :=
    CompatibleAtlasPresentation.localizationFunctor
  let W : MorphismProperty K.CompatibleCategory.{u, v} :=
    CompatibleAtlasPresentation.quasiIsomorphisms
  let S : K.CompatibleCategory.{u, v} ⥤ SaturatedAtlasPresentation.{u, max u v, max u v} K :=
    CompatibleAtlasPresentation.saturationFunctor
  let T : L.CompatibleCategory.{u, v} ⥤ SaturatedAtlasPresentation.{u, max u v, max u v} L :=
    CompatibleAtlasPresentation.saturationFunctor
  let R : SaturatedAtlasPresentation.{u, max u v, max u v} L ⥤ _ :=
    SaturatedAtlasPresentation.localizationFunctor
  let F := (CompatibleAtlasPresentation.localizedSaturationFunctor :
    K.CompatibleAnalyticCategory.{u, v} ⥤ _) ⋙ localizedFunctor K L
  let G := localizedExtend.{u, v} e ⋙ CompatibleAtlasPresentation.localizedSaturationFunctor
  let C := S ⋙ saturatedLocalizedFunctor K L
  let D := compatibleExtend.{u, v} e ⋙ T ⋙ R
  have hF : Q ⋙ F = C := by
    change (Q ⋙ CompatibleAtlasPresentation.localizedSaturationFunctor) ⋙ localizedFunctor K L = _
    rw [CompatibleAtlasPresentation.localizationFunctor_localizedSaturationFunctor]
    change S ⋙ (SaturatedAtlasPresentation.localizationFunctor ⋙ localizedFunctor K L) = C
    rw [localizationFunctor_localizedFunctor]
  have hG : Q ⋙ G = D := by
    change (Q ⋙ localizedExtend e) ⋙ CompatibleAtlasPresentation.localizedSaturationFunctor = _
    rw [localizedExtend_factor]
    change compatibleExtend e ⋙
      (CompatibleAtlasPresentation.localizationFunctor ⋙
        CompatibleAtlasPresentation.localizedSaturationFunctor) = D
    rw [CompatibleAtlasPresentation.localizationFunctor_localizedSaturationFunctor]
  letI : Localization.Lifting Q W C F := ⟨eqToIso hF⟩
  letI : Localization.Lifting Q W D G := ⟨eqToIso hG⟩
  let comparison : C ≅ D :=
    (Functor.isoWhiskerRight (saturationForgetIso K) D) ≪≫ Functor.leftUnitor D
  exact Localization.liftNatIso Q W C D F G comparison

end CompleteUltrametricField
end Langlands.Analytic
