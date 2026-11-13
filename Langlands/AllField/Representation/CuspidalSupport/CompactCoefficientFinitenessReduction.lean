import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction
import Langlands.AllField.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement
import Langlands.AllField.Representation.Smooth.SmallRealizationProof
/-!
# Reduction of fixed-level finiteness on `G°` to the corner structure and dimension bound

Bernstein--Zelevinsky (1976), Theorem 4.14 via 4.16, page 41: the sandwich structure of
compact-open Hecke corners of `G°` (Lemma 4.9) and the dimension bound for simple modules
over sandwich algebras (Lemma 4.10, §4.11) imply that every compact open subgroup of `G°`
has a nonzero fixed vector in only finitely many compact-coefficient classes.
-/

noncomputable section

namespace Langlands.AllField

open MeasureTheory

universe uG uV uF

namespace CompactCoefficientClass
open Langlands.CompactCoefficientClass
open Langlands.AllField.CompactCoefficientClass

variable {G : Type uG} [Group G] [TopologicalSpace G]

end CompactCoefficientClass

namespace CuspidalSupport
open Langlands.CuspidalSupport hiding CompactCoefficientFixedLevelFinitenessTheorem DeterminantUnitCornerStructureStatement compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.CompactCoefficientClass
open Langlands.AllField.CompactCoefficientClass

/-- Bernstein--Zelevinsky (1976), 4.14 via 4.16: the corner structure statement for `G°`
and the sandwich dimension bound imply fixed-level finiteness of compact-coefficient
classes on `G°`. -/
theorem compactCoefficientFixedLevelFiniteness_of_cornerStructure
    (hA : DeterminantUnitCornerStructureStatement.{uF})
    (hB : SandwichSimpleModuleDimensionBoundStatement.{uF, uV}) :
    CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV} := by
  intro F _ T n _ B
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

end Langlands.AllField
