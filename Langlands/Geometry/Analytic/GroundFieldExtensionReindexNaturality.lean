import Langlands.Geometry.Analytic.GroundFieldExtensionReindex
import Langlands.Geometry.Analytic.GroundFieldExtensionFunctor

/-! # Ground field extension commutes with relabeling the full maps -/

noncomputable section

universe u v w t u'

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {I J : Type t} (eA : I ≃ A.atlas.Index) (eB : J ≃ B.atlas.Index)

/-- Reindexing retains the complete original bounded pullback compatibility. -/
def CompatibleStrongHom.reindex (f : CompatibleStrongHom A B) :
    CompatibleStrongHom (A.reindex eA) (B.reindex eB) where
  toStrongHom := f.toStrongHom.reindex eA eB
  compatible i j k hj hk m hmj hmk := f.compatible (eA i) (eB j) (eB k) hj hk (eB m) hmj hmk

namespace GroundFieldExtension

open IndexedAffinoidAtlas.GroundFieldExtension (presentation chartSystem reindexHomeomorph)

variable (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (f : CompatibleStrongHom A B)

/-- On the actual quotients the extended relabeled map commutes with the
reindexing homeomorphisms. The chosen representative calculation uses the
same bounded pullback before relabeling. -/
theorem reindexHomeomorph_compatibleMap (x : (presentation K L (A.reindex eA).atlas).space) :
    reindexHomeomorph K L B.atlas eB ((compatibleMap K L (f.reindex eA eB)).baseMap x) =
      (compatibleMap K L f).baseMap (reindexHomeomorph K L A.atlas eA x) := by
  obtain ⟨i, s, rfl⟩ := (chartSystem K L (A.reindex eA).atlas).exists_chart x
  obtain ⟨j, hj⟩ := (f.reindex eA eB).target_exists i
  let g := f.reindex eA eB
  have hi : f.baseMap '' range (A.atlas.chart (eA i)) ⊆ range (B.atlas.chart (eB j)) := hj
  change reindexHomeomorph K L B.atlas eB
      (pointMap K L g.toStrongHom g.compatible ((chartSystem K L (A.reindex eA).atlas).chart i s)) =
    pointMap K L f.toStrongHom f.compatible ((chartSystem K L A.atlas).chart (eA i) s)
  exact (congrArg (reindexHomeomorph K L B.atlas eB)
    (pointMap_chart K L g.toStrongHom g.compatible i j hj s)).trans
    (pointMap_chart K L f.toStrongHom f.compatible (eA i) (eB j) hi s).symm

/-- At corresponding admissible pairs, the two extended maps have literally
the same bounded pullback between the same extended algebras. -/
theorem compatibleMap_reindex_pullback (i : I) (j : J)
    (h : (compatibleMap K L (f.reindex eA eB)).baseMap ''
      range ((presentation K L (A.reindex eA).atlas).atlas.chart i) ⊆
      range ((presentation K L (B.reindex eB).atlas).atlas.chart j))
    (h' : (compatibleMap K L f).baseMap ''
      range ((presentation K L A.atlas).atlas.chart (eA i)) ⊆
      range ((presentation K L B.atlas).atlas.chart (eB j))) :
    (compatibleMap K L (f.reindex eA eB)).pullback i j h =
      (compatibleMap K L f).pullback (eA i) (eB j) h' := rfl

end GroundFieldExtension
end Langlands.Analytic.AffinoidAtlasPresentation
