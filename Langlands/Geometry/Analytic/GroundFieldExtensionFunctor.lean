import Langlands.Geometry.Analytic.GroundFieldExtensionMaps
import Langlands.Geometry.Analytic.CompatibleStrongSaturationFunctor
import Langlands.Geometry.Analytic.SaturatedStrongLocalization

/-! # The ground field extension functor on compatible and saturated atlases -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open CategoryTheory Set Topology PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension
open IndexedAffinoidAtlas.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

theorem pointMap_id (A : AffinoidAtlasPresentation.{u, v, w} K)
    (z : (chartSystem K L A.atlas).Space) :
    pointMap K L (CompatibleStrongHom.id A).toStrongHom
      (CompatibleStrongHom.id A).compatible z = z := by
  obtain ⟨i, s, rfl⟩ := (chartSystem K L A.atlas).exists_chart z
  have hi : (CompatibleStrongHom.id A).baseMap '' range (A.atlas.chart i) ⊆
      range (A.atlas.chart i) := by
    change (StrongHom.id A).baseMap '' _ ⊆ _
    simp only [StrongHom.id, ContinuousMap.coe_id, image_id, Subset.rfl]
  rw [pointMap_chart K L (CompatibleStrongHom.id A).toStrongHom
    (CompatibleStrongHom.id A).compatible i i hi]
  unfold chartMap
  have heq : map K L ((CompatibleStrongHom.id A).pullback i i hi) =
      BoundedAlgHom.id L (chartAlgebra K L A.atlas i) := by
    change map K L (A.atlas.restriction i i _) = _
    rw [A.atlas.restriction_id, map_id]
  rw [heq]
  congr 1

theorem compatibleMap_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    compatibleMap K L (CompatibleStrongHom.id A) =
      CompatibleStrongHom.id (presentation K L A.atlas) := by
  have hb : (compatibleMap K L (CompatibleStrongHom.id A)).baseMap =
      ContinuousMap.id (presentation K L A.atlas).space := by
    ext z
    exact pointMap_id K L A z
  refine CompatibleStrongHom.ext_of_pullback hb ?_
  intro (i : A.atlas.Index)
  have hi : (compatibleMap K L (CompatibleStrongHom.id A)).baseMap ''
      range ((chartSystem K L A.atlas).chart i) ⊆
        range ((chartSystem K L A.atlas).chart i) := by
    rw [hb]
    simp only [ContinuousMap.coe_id, image_id, Subset.rfl]
  refine ⟨i, hi, ?_⟩
  rfl

theorem pointMap_comp {A B C : AffinoidAtlasPresentation.{u, v, w} K}
    (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C)
    (z : (chartSystem K L A.atlas).Space) :
    pointMap K L (f.comp g).toStrongHom (f.comp g).compatible z =
      pointMap K L g.toStrongHom g.compatible
        (pointMap K L f.toStrongHom f.compatible z) := by
  obtain ⟨i, s, rfl⟩ := (chartSystem K L A.atlas).exists_chart z
  obtain ⟨j, hj⟩ := f.target_exists i
  obtain ⟨k, hk⟩ := g.target_exists j
  have hfg := f.toStrongHom.comp_admissible g.toStrongHom i j k hj hk
  rw [pointMap_chart K L f.toStrongHom f.compatible i j hj]
  change pointMap K L (f.comp g).toStrongHom (f.comp g).compatible
      ((chartSystem K L A.atlas).chart i s) =
    pointMap K L g.toStrongHom g.compatible
      ((chartSystem K L B.atlas).chart j
        (BanachSpectrum.comap (map K L (f.pullback i j hj)).toBoundedRingHom s))
  rw [pointMap_chart K L g.toStrongHom g.compatible j k hk,
    pointMap_chart K L (f.comp g).toStrongHom (f.comp g).compatible i k hfg]
  unfold chartMap
  rw [CompatibleStrongHom.comp_pullback f g i j k hj hk hfg, map_comp]
  rfl

theorem compatibleMap_comp {A B C : AffinoidAtlasPresentation.{u, v, w} K}
    (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C) :
    compatibleMap K L (f.comp g) =
      (compatibleMap K L f).comp (compatibleMap K L g) := by
  have hb : (compatibleMap K L (f.comp g)).baseMap =
      (compatibleMap K L g).baseMap.comp
        (compatibleMap K L f).baseMap := by
    ext z
    exact pointMap_comp K L f g z
  refine CompatibleStrongHom.ext_of_pullback hb ?_
  intro i
  obtain ⟨j, hj⟩ := f.target_exists i
  obtain ⟨k, hk⟩ := g.target_exists j
  have hfg := f.toStrongHom.comp_admissible g.toStrongHom i j k hj hk
  have hjL := (admissible_iff K L f.toStrongHom f.compatible i j).2 hj
  have hkL := (admissible_iff K L g.toStrongHom g.compatible j k).2 hk
  have hfgL := (admissible_iff K L
    (f.comp g).toStrongHom (f.comp g).compatible i k).2 hfg
  refine ⟨k, hfgL, ?_⟩
  rw [CompatibleStrongHom.comp_pullback
    (compatibleMap K L f) (compatibleMap K L g)
      i j k hjL hkL]
  change map K L ((f.comp g).pullback i k _) =
    (map K L (f.pullback i j hj)).comp (map K L (g.pullback j k hk))
  rw [CompatibleStrongHom.comp_pullback f g i j k hj hk, map_comp]

/-- Ground field extension on all presentations with compatible strong maps. -/
def compatibleFunctor : CompatibleAtlasPresentation.{u, v, w} K ⥤
    CompatibleAtlasPresentation.{u', max u' w, w} L where
  obj A := ⟨presentation K L A.presentation.atlas⟩
  map f := compatibleMap K L f
  map_id A := compatibleMap_id K L A.presentation
  map_comp f g := compatibleMap_comp K L f g

/-- Every strong map between saturated source presentations is included.
The target is saturated and then localized by the Library functors. -/
def saturatedLocalizedFunctor : SaturatedAtlasPresentation.{u, v, w} K ⥤
    SaturatedAtlasPresentation.LocalizedCategory.{u', max u' w, max u' w} (K := L) :=
  SaturatedAtlasPresentation.compatibleFunctor ⋙
    compatibleFunctor K L ⋙
    CompatibleAtlasPresentation.saturationFunctor ⋙
    SaturatedAtlasPresentation.localizationFunctor

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
