import Langlands.Representation.Aubert.General.PadicMatrixAlternatingOperatorSpecializationStatement
import Langlands.Representation.Aubert.General.PadicMatrixFunctorSpecializationProof

/-! # Specialization of the local-field matrix alternating sum to the p-adic operator -/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RationalPointFamily.GL

section Rankwise

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
  (n : ℕ)

/-- The p-adic matrix functors supply the finite-length and short exact
sequence preservation witnesses for the local-field operator. -/
theorem localFieldMatrixParabolicExactLength_padic :
    LocalFieldMatrixParabolicExactLength.{u, v} T.toLocalFieldData n := by
  intro B
  obtain ⟨_, _, hIndLength, hIndExact, hJacLength, hJacExact, _⟩ :=
    padicMatrixFunctorSpecialization.{u, v} F T n B
  exact ⟨hIndLength, hIndExact, hJacLength, hJacExact⟩

/-- Both unadjusted operators agree on the same exact Grothendieck group
for every matrix preservation witness. -/
theorem localFieldMatrixAlternatingOperator_eq_padic
    (h : LocalFieldMatrixParabolicExactLength.{u, v} T.toLocalFieldData n) :
    letI := T.topology
    localFieldMatrixAlternatingOperator T.toLocalFieldData n h =
      Aubert.alternatingOperator.{u, max (u + 1) v} F T n := by
  let := T.topology
  let : Fintype (Langlands.GeneralLinear.BlockShape n) := Fintype.ofFinite _
  rw [localFieldMatrixAlternatingOperator, Aubert.alternatingOperator_eq_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  obtain ⟨_, _, _, _, _, _, hMaps⟩ := padicMatrixFunctorSpecialization.{u, v} F T n B
  obtain ⟨hIndMap, hJacMap⟩ := hMaps (h B).1 (h B).2.1 (h B).2.2.1 (h B).2.2.2
  rw [hIndMap, hJacMap]
  rfl

end Rankwise

/-- The exact p-adic specialization of the actual matrix alternating sum. -/
theorem padicMatrixAlternatingOperatorSpecialization :
    PadicMatrixAlternatingOperatorSpecializationStatement.{u, v} := by
  intro p _ F T n
  exact ⟨localFieldMatrixParabolicExactLength_padic F T n,
    localFieldMatrixAlternatingOperator_eq_padic F T n⟩

end Langlands.Aubert.General.RationalPointFamily.GL
