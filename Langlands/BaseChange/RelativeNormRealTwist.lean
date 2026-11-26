import Langlands.BaseChange.ExtensionInvariants
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.LocalField.RelativeIntegers
import Langlands.LocalField.PadicBridge
import Langlands.AllField.Group.GL.NormalizedCharacter
import Langlands.Representation.Twist.RealPower

/-! # Residue degree and real determinant twists on a relative p-adic field -/

noncomputable section

namespace Langlands.BaseChange

universe u v
variable {p : ℕ} [Fact p.Prime]
  {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

/-- The residue field of the upper field has positive degree over that of the base.
This is the residue-cardinality relation in `IsResidueDegree`. -/
theorem exists_pos_residueDegree :
    haveI := T.valuativeRel
    haveI := S.valuativeRel
    ∃ f : ℕ, 0 < f ∧ IsResidueDegree F.Carrier E.Carrier f := by
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.relativeResidueAlgebra S
  let := T.finite_residueField
  let := S.finite_residueField
  exact ⟨Module.finrank T.ResidueField S.ResidueField, Module.finrank_pos,
    Module.natCard_eq_pow_finrank (K := T.ResidueField) (V := S.ResidueField)⟩

variable [FiniteDimensional F.Carrier E.Carrier]

private theorem normalizedAbsUnits_comp_relativeNorm :
    T.toLocalFieldData.normalizedAbsUnits.comp (Units.map (Algebra.norm F.Carrier : E.Carrier →* F.Carrier)) =
      S.toLocalFieldData.normalizedAbsUnits := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  apply NNReal.eq
  exact LocalClassField.normalizedAbs_relative_norm F E T S (x : E.Carrier)

/-- Pullback of a real power of the normalized absolute value by the relative
norm equals the same real power of the upper normalized absolute value. -/
theorem realPowerCharacter_comp_relativeNorm (t : ℝ) :
    (realPowerCharacter T.toLocalFieldData.normalizedAbsUnits t).comp
      (Units.map (Algebra.norm F.Carrier : E.Carrier →* F.Carrier)) =
      realPowerCharacter S.toLocalFieldData.normalizedAbsUnits t := by
  unfold realPowerCharacter
  rw [MonoidHom.comp_assoc, normalizedAbsUnits_comp_relativeNorm T S]

end Langlands.BaseChange
