import Langlands.AllFieldBZ.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement
import Langlands.AllFieldBZ.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ
open MeasureTheory
universe uG uV uF

namespace CompactCoefficientClass
open Langlands.CompactCoefficientClass
variable {G : Type uG} [Group G] [TopologicalSpace G]

end CompactCoefficientClass
namespace CuspidalSupport
open Langlands.CuspidalSupport hiding CompactCoefficientFixedLevelFinitenessTheorem DeterminantUnitCornerStructureStatement compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
open Langlands.CompactCoefficientClass
/-- Bernstein--Zelevinsky (1976), 4.14 via 4.16: the corner structure statement for `G°`
and the sandwich dimension bound imply fixed-level finiteness of compact-coefficient
classes on `G°`. -/
theorem compactCoefficientFixedLevelFiniteness_of_cornerStructure
    (hA : DeterminantUnitCornerStructureStatement.{uF})
    (hB : SandwichSimpleModuleDimensionBoundStatement.{uF, uV}) :
    CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV} := by
  intro F T n _ B
  let _ := T.topology
  have := T.leviTopologicalGroup B
  let _ : MeasurableSpace (determinantUnitSubgroup T B) := borel _
  have : BorelSpace (determinantUnitSubgroup T B) := ⟨rfl⟩
  intro K hK
  obtain ⟨N, hN, hNK, hcorner⟩ := hA F T n B K hK
  let K₀ : TopologicalSpace.PositiveCompacts (determinantUnitSubgroup T B) :=
    ⟨⟨K, hK⟩, ⟨1, by rw [K.isOpen.interior_eq]; exact K.one_mem⟩⟩
  obtain ⟨q, l, x, a, ha, hspan⟩ := hcorner (Measure.haarMeasure K₀)
  exact (fixedStratum_finite_of_sandwich (Measure.haarMeasure K₀) N hN hB x a ha hspan).subset
    (fixedStratum_mono hNK)

end CuspidalSupport
end Langlands.AllFieldBZ
