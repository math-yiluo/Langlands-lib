import Langlands.Group.GL.MirabolicTailConullProof
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Group.GL.PadicBlocksSupplement
/-!
# Proof of the open full-measure inverse-row tail locus

Openness follows from continuity of inversion and of matrix entries. The
exceptional set is covered by finitely many pieces with a nonzero head
coordinate; an elementary transvection with a small nonzero parameter moves
each piece off itself, so Steinhaus's theorem makes each piece null.
See the paired Markdown for the full route.
-/

namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear

open _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Set
open scoped Pointwise

universe uF

section Steinhaus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

end Steinhaus

section Transvection

variable {K : Type*} [Field K] {n : ℕ}

variable [TopologicalSpace K] [IsTopologicalRing K]

end Transvection

section Padic

variable {F : Type uF} [Field F]

/-- Every neighbourhood of zero in the supplied topology contains a nonzero
element. A neighbourhood of zero contains a valuation ball `{x | v x < v a}` with
`a ≠ 0`; multiplying `a` by an element of valuation less than one (the valuation is
nontrivial) gives a nonzero element of that ball. -/
theorem padic_exists_ne_zero_mem_nhds_zero (T : LocalFieldData F) :
    letI := T.topology
    ∀ U ∈ 𝓝 (0 : F), ∃ t ∈ U, t ≠ 0 := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  intro U hU
  obtain ⟨γ, hγ, hγU⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mp hU
  obtain ⟨a, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation F)
  have ha : a ≠ 0 := by simpa using hγ
  have hr : r ≠ 0 := by simpa using hr0
  refine ⟨a * r, hγU ?_, mul_ne_zero ha hr⟩
  change ValuativeRel.valuation F (a * r) < ValuativeRel.valuation F a
  rw [map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.mpr hγ) hr1

end Padic

end Langlands.AllField.GeneralLinear
