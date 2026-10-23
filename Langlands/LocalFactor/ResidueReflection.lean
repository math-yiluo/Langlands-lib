import Langlands.LocalFactor.WeilDelignePair
import Langlands.LocalField.Canonical
import Langlands.LocalField.Normalization.Proof

/-!
# Reflection at the canonical residue cardinality

The common reciprocal scale for arithmetic and representation-side gamma factors.
-/

noncomputable section

namespace Langlands.LocalFactor

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The unit `q⁻¹` for the canonical residue cardinality `q`: the reflection
`X ↦ q⁻¹ / X` corresponds to `s ↦ 1 - s` at `X = q^(-s)`. -/
def residueReflection : ℂˣ :=
  WeilDeligne.reflectionScale (F.canonicalTopologicalData.residueCardinality : ℝ)
    (by exact_mod_cast Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one)

@[simp]
theorem coe_residueReflection :
    (residueReflection F : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ)⁻¹ := by
  simp [residueReflection]

end Langlands.LocalFactor
