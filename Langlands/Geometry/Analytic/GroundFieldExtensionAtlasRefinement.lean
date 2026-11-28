import Langlands.Geometry.Analytic.GroundFieldExtensionAtlas
import Langlands.Geometry.Analytic.SaturatedDomainSite
import Langlands.Geometry.Analytic.CommonSubatlas

/-! # Scalar extension of chart refinements -/

noncomputable section

universe u u' v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : Type v} [TopologicalSpace X] (d : IndexedAffinoidAtlas.{u, v, w} K X)

private theorem selectedChartFamily_eq_preimage (P : d.Index → Prop) :
    (atlas K L d).selectedChartFamily P = (fun U => projection K L d ⁻¹' U) '' d.selectedChartFamily P := by
  ext U
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨range (d.chart i.val), ⟨i, rfl⟩, (range_chart K L d i.val).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, range_chart K L d i.val⟩

private theorem chartFamily_eq_preimage :
    range (fun i => range ((atlas K L d).chart i)) =
      (fun U => projection K L d ⁻¹' U) '' range (fun i => range (d.chart i)) := by
  ext U
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨range (d.chart i), ⟨i, rfl⟩, (range_chart K L d i).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, range_chart K L d i⟩

/-- A relative finite chart refinement still refines after scalar extension,
using the original index predicate. -/
theorem isLocallyRefiningSelection_extend {P : d.Index → Prop} (hP : d.IsLocallyRefiningSelection P) :
    (atlas K L d).IsLocallyRefiningSelection P := by
  have hp := AtlasTopology.LocallyRefines.preimage hP (projection K L d) (continuous_projection K L d)
  exact Eq.mpr (congrArg₂ AtlasTopology.LocallyRefines (selectedChartFamily_eq_preimage K L d P)
    (chartFamily_eq_preimage K L d)) hp

/-- Extend a whole downward-closed locally refining chart selection,
retaining exactly the selected original indices. -/
def extendRefiningSelection (P : d.RefiningSelection) : (atlas K L d).RefiningSelection where
  carrier := P.carrier
  downward_closed i j h := P.downward_closed i j ((range_chart_subset_iff K L d i j).mp h)
  locally_refining := isLocallyRefiningSelection_extend K L d P.locally_refining

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension
