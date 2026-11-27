import Langlands.Correspondence.Laumon.Completion
import Langlands.FieldTheory.DenseSeparableGeneration
import Langlands.Galois.RestrictAlongTower
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # The absolute Galois group of a henselian end and of its completion -/

noncomputable section

open Langlands.FieldTheory
open scoped WithZero Valued

namespace Langlands.Henniart.Laumon

universe u

/-- Restriction from the absolute Galois group of the completed end to that of the
henselian end is a homeomorphism for the Krull topologies. -/
theorem henselianCompletionGalois : HenselianCompletionGaloisStatement.{u} := by
  intro k _
  have hdense : DenseRange (algebraMap (endField k) (LaurentSeries k)) := by
    refine (LaurentSeries.coe_range_dense (K := k)).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨algebraMap (RatFunc k) (endField k) x, rfl⟩
  let := Langlands.LocalField.Laurent.valuationRankOne k
  let : NormedField (LaurentSeries k) := Valued.toNormedField (LaurentSeries k) (ℤᵐ⁰)
  have hgen : IntermediateField.adjoin (LaurentSeries k)
      (endGenericClosure k : Set (SeparableClosure (LaurentSeries k))) = ⊤ :=
    (adjoin_separableClosure_of_denseRange hdense (SeparableClosure (LaurentSeries k))).trans
      ((separableClosure.eq_top_iff _ _).mpr inferInstance)
  exact isHomeomorph_restrictNormalHom_of_tower (endGenericClosure k)
    (separableClosure.separableClosure_eq_bot (RatFunc k) (LaurentSeries k)) hgen

end Langlands.Henniart.Laumon
