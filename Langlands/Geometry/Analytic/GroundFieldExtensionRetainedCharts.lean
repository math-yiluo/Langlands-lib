import Langlands.Geometry.Analytic.GroundFieldExtensionReindexNaturality
import Langlands.Geometry.Analytic.StrongSourceRestriction

/-! # Retained charts with indices in the ambient extension universe -/

noncomputable section

universe u u' v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open Set
open IndexedAffinoidAtlas.GroundFieldExtension (presentation)

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- The original retained scalar-extended charts with only the index universe raised. -/
abbrev retainedPresentation (A : AffinoidAtlasPresentation.{u, v, w} K) :
    AffinoidAtlasPresentation.{u', max u' w, max u' w} L :=
  (presentation K L A.atlas).saturationSource

/-- Relabel the complete scalar-extended map, retaining all bounded pullbacks. -/
abbrev retainedMap (f : CompatibleStrongHom A B) :
    CompatibleStrongHom (retainedPresentation K L A) (retainedPresentation K L B) :=
  CompatibleStrongHom.reindex (A := presentation K L A.atlas) (B := presentation K L B.atlas)
    (Equiv.ulift : ULift.{max u' w} A.atlas.Index ≃ A.atlas.Index)
    (Equiv.ulift : ULift.{max u' w} B.atlas.Index ≃ B.atlas.Index)
    (compatibleMap K L f)

/-- Original and retained-chart admissibility are equivalent. -/
theorem retainedMap_admissible_iff (f : CompatibleStrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index) :
    (retainedMap K L f).baseMap '' range ((retainedPresentation K L A).atlas.chart (ULift.up i)) ⊆
      range ((retainedPresentation K L B).atlas.chart (ULift.up j)) ↔
        f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j) :=
  admissible_iff K L f.toStrongHom f.compatible i j

/-- Composition of the retained maps retains the full scalar-extended composite. -/
theorem retainedMap_comp (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C) :
    retainedMap K L (f.comp g) = (retainedMap K L f).comp (retainedMap K L g) := by
  have h := compatibleMap_comp K L f g
  let F := compatibleMap K L f
  let G := compatibleMap K L g
  let H := compatibleMap K L (f.comp g)
  have hbase : H.baseMap = (F.comp G).baseMap := congrArg (fun m => m.baseMap) h
  refine CompatibleStrongHom.ext_of_pullback hbase fun i => ?_
  let F' := retainedMap K L f
  let G' := retainedMap K L g
  obtain ⟨j, hj⟩ := F.target_exists i.down
  obtain ⟨k, hk⟩ := G.target_exists j
  have hc := F.toStrongHom.comp_admissible G.toStrongHom i.down j k hj hk
  have hc' : H.baseMap '' range ((presentation K L A.atlas).atlas.chart i.down) ⊆
      range ((presentation K L C.atlas).atlas.chart k) :=
    hbase.symm ▸ hc
  refine ⟨ULift.up k, hc', ?_⟩
  exact (StrongHom.pullback_congr (congrArg CompatibleStrongHom.toStrongHom h) i.down k hc' hc).trans
    ((CompatibleStrongHom.comp_pullback F G i.down j k hj hk hc).trans
      (CompatibleStrongHom.comp_pullback F' G' i (ULift.up j) (ULift.up k) hj hk _).symm)

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
