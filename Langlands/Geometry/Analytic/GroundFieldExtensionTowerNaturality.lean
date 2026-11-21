import Langlands.Geometry.Analytic.GroundFieldExtensionStrongTower
import Langlands.Geometry.Analytic.GroundFieldExtensionFunctor

/-! # Naturality of the tower comparison in compatible strong maps -/

noncomputable section

universe u u' u'' v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open CategoryTheory Set Topology
open PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension
open IndexedAffinoidAtlas.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (M : Type u'') [NormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [NormedAlgebra K M] [IsScalarTower K L M]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The tower homeomorphisms intertwine the direct and successive point maps
of every compatible strong map. -/
theorem towerHomeomorph_pointMap (f : CompatibleStrongHom A B)
    (z : (chartSystem K M A.atlas).Space) :
    towerHomeomorph K L M B.atlas (pointMap K M f.toStrongHom f.compatible z) =
      pointMap L M (compatibleMap K L f).toStrongHom (compatibleMap K L f).compatible
        (towerHomeomorph K L M A.atlas z) := by
  obtain ⟨i, s, rfl⟩ := (chartSystem K M A.atlas).exists_chart z
  obtain ⟨j, hj⟩ := f.target_exists i
  have hjL := (admissible_iff K L f.toStrongHom f.compatible i j).2 hj
  have h₁ : pointMap K M f.toStrongHom f.compatible ((chartSystem K M A.atlas).chart i s) =
      (chartSystem K M B.atlas).chart j
        (BanachSpectrum.comap (map K M (f.pullback i j hj)).toBoundedRingHom s) :=
    pointMap_chart K M f.toStrongHom f.compatible i j hj s
  have h₂ : pointMap L M (compatibleMap K L f).toStrongHom (compatibleMap K L f).compatible
      ((chartSystem L M (presentation K L A.atlas).atlas).chart i (towerChartHomeomorph K L M A.atlas i s)) =
      (chartSystem L M (presentation K L B.atlas).atlas).chart j
        (BanachSpectrum.comap (map L M (map K L (f.pullback i j hj))).toBoundedRingHom
          (towerChartHomeomorph K L M A.atlas i s)) :=
    pointMap_chart L M (compatibleMap K L f).toStrongHom (compatibleMap K L f).compatible
      i j hjL _
  refine ((congrArg (towerHomeomorph K L M B.atlas) h₁).trans ?_).trans h₂.symm
  exact congrArg ((chartSystem L M (presentation K L B.atlas).atlas).chart j)
    (towerSpectrumHomeomorph_naturality K L M (f.pullback i j hj) s)

/-- The compatible tower comparison is natural: extending a compatible
strong map directly and then comparing agrees with comparing and then
extending it successively, as an equality of compatible strong maps with
all their bounded pullbacks. -/
theorem towerCompatibleHom_natural (f : CompatibleStrongHom A B) :
    (towerCompatibleHom K L M A.atlas).comp (compatibleMap L M (compatibleMap K L f)) =
      (compatibleMap K M f).comp (towerCompatibleHom K L M B.atlas) := by
  have hb : ((towerCompatibleHom K L M A.atlas).comp
      (compatibleMap L M (compatibleMap K L f))).baseMap =
      ((compatibleMap K M f).comp (towerCompatibleHom K L M B.atlas)).baseMap := by
    ext z
    exact (towerHomeomorph_pointMap K L M f z).symm
  refine CompatibleStrongHom.ext_of_pullback hb ?_
  intro (i : A.atlas.Index)
  obtain ⟨j, hj⟩ := f.target_exists i
  have hjL := (admissible_iff K L f.toStrongHom f.compatible i j).2 hj
  have hjM := (admissible_iff L M (compatibleMap K L f).toStrongHom
    (compatibleMap K L f).compatible i j).2 hjL
  have hjD := (admissible_iff K M f.toStrongHom f.compatible i j).2 hj
  have htA := (towerAdmissible_iff K L M A.atlas i i).2 subset_rfl
  have htB := (towerAdmissible_iff K L M B.atlas j j).2 subset_rfl
  have h := (towerCompatibleHom K L M A.atlas).toStrongHom.comp_admissible
    (compatibleMap L M (compatibleMap K L f)).toStrongHom i i j htA hjM
  refine ⟨j, h, ?_⟩
  have e₁ : ((towerCompatibleHom K L M A.atlas).comp
      (compatibleMap L M (compatibleMap K L f))).pullback i j h =
      (towerChartEquiv K L M A.atlas i).toBoundedAlgHom.comp
        (map L M (map K L (f.pullback i j hj))) :=
    (CompatibleStrongHom.comp_pullback (towerCompatibleHom K L M A.atlas)
      (compatibleMap L M (compatibleMap K L f)) i i j htA hjM h).trans
      (congrArg (fun φ => φ.comp ((compatibleMap L M (compatibleMap K L f)).pullback i j hjM))
        (towerCompatibleHom_pullback_same K L M A.atlas i htA))
  have e₂ : ∀ h', ((compatibleMap K M f).comp (towerCompatibleHom K L M B.atlas)).pullback
      i j h' = (map K M (f.pullback i j hj)).comp
        (towerChartEquiv K L M B.atlas j).toBoundedAlgHom := fun h' =>
    (CompatibleStrongHom.comp_pullback (compatibleMap K M f)
      (towerCompatibleHom K L M B.atlas) i j j hjD htB h').trans
      (congrArg (fun φ => ((compatibleMap K M f).pullback i j hjD).comp φ)
        (towerCompatibleHom_pullback_same K L M B.atlas j htB))
  exact e₁.trans ((towerEquiv_naturality K L M (f.pullback i j hj)).trans (e₂ _).symm)

/-- The tower comparison at one presentation, as an isomorphism in the
category of compatible strong maps. -/
def towerIso (P : CompatibleAtlasPresentation.{u, v, w} K) :
    (compatibleFunctor K M).obj P ≅ (compatibleFunctor K L ⋙ compatibleFunctor L M).obj P where
  hom := towerCompatibleHom K L M P.presentation.atlas
  inv := towerCompatibleInv K L M P.presentation.atlas
  hom_inv_id := towerCompatibleHom_comp_inv K L M P.presentation.atlas
  inv_hom_id := towerCompatibleInv_comp_hom K L M P.presentation.atlas

/-- The forward component is the compatible tower comparison. -/
theorem towerIso_hom (P : CompatibleAtlasPresentation.{u, v, w} K) :
    (towerIso K L M P).hom = towerCompatibleHom K L M P.presentation.atlas := rfl

/-- Direct ground field extension from `K` to `M` is naturally isomorphic,
on compatible presentations and compatible strong maps, to extension from
`K` to `L` followed by extension from `L` to `M`. -/
def towerNatIso :
    (compatibleFunctor K M : CompatibleAtlasPresentation.{u, v, w} K ⥤ _) ≅
      compatibleFunctor K L ⋙ compatibleFunctor L M :=
  NatIso.ofComponents (towerIso K L M) fun {_ _} f =>
    (towerCompatibleHom_natural K L M f).symm

/-- The components of the natural isomorphism are the tower comparisons. -/
theorem towerNatIso_hom_app (P : CompatibleAtlasPresentation.{u, v, w} K) :
    (towerNatIso K L M).hom.app P = towerCompatibleHom K L M P.presentation.atlas := rfl

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
