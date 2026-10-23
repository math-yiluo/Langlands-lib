import Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
import Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement

/-!
# Reduction of fixed-level finiteness on `G°` to the corner structure and dimension bound

Bernstein--Zelevinsky (1976), Theorem 4.14 via 4.16, page 41: the sandwich structure of
compact-open Hecke corners of `G°` (Lemma 4.9) and the dimension bound for simple modules
over sandwich algebras (Lemma 4.10, §4.11) imply that every compact open subgroup of `G°`
has a nonzero fixed vector in only finitely many compact-coefficient classes.
-/

noncomputable section

namespace Langlands

open MeasureTheory

universe uG uV uF

namespace CompactCoefficientClass

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A class with a nonzero `K`-fixed vector has a nonzero `N`-fixed vector for `N ≤ K`. -/
theorem fixedStratum_mono {N K : Subgroup G} (h : N ≤ K) :
    fixedStratum.{uG, uV} K ⊆ fixedStratum.{uG, uV} N := by
  intro c hc
  obtain ⟨A, rfl⟩ := Quotient.exists_rep c
  change fixedVectors A.obj.representation K ≠ ⊥ at hc
  change fixedVectors A.obj.representation N ≠ ⊥
  intro h0
  apply hc
  rw [eq_bot_iff, ← h0]
  intro v hv
  exact fun k => hv ⟨k, h k.property⟩

end CompactCoefficientClass

namespace CuspidalSupport

open GeneralLinear CompactCoefficientClass

/-- Bernstein--Zelevinsky (1976), 4.14 via 4.16: the corner structure statement for `G°`
and the sandwich dimension bound imply fixed-level finiteness of compact-coefficient
classes on `G°`. -/
theorem compactCoefficientFixedLevelFiniteness_of_cornerStructure
    (hA : DeterminantUnitCornerStructureStatement.{uF})
    (hB : SandwichSimpleModuleDimensionBoundStatement.{uF, uV}) :
    CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV} := by
  intro p _ F T n _ B
  let _ := T.topology
  have := T.leviTopologicalGroup B
  let _ : MeasurableSpace (determinantUnitSubgroup T B) := borel _
  have : BorelSpace (determinantUnitSubgroup T B) := ⟨rfl⟩
  intro K hK
  obtain ⟨N, hN, hNK, hcorner⟩ := hA p F T n B K hK
  let K₀ : TopologicalSpace.PositiveCompacts (determinantUnitSubgroup T B) :=
    ⟨⟨K, hK⟩, ⟨1, by rw [K.isOpen.interior_eq]; exact K.one_mem⟩⟩
  obtain ⟨q, l, x, a, ha, hspan⟩ := hcorner (Measure.haarMeasure K₀)
  exact (fixedStratum_finite_of_sandwich (Measure.haarMeasure K₀) N hN hB x a ha hspan).subset
    (fixedStratum_mono hNK)

end CuspidalSupport

end Langlands
