import Langlands.LocalFactor.ResidueReflection
import Langlands.AllField.LocalField.Foundation
/-!
# Reflection at the canonical residue cardinality

The common reciprocal scale for arithmetic and representation-side gamma factors.
-/

noncomputable section

namespace Langlands.AllField.LocalFactor
open Langlands.LocalFactor hiding coe_residueReflection residueReflection
open Langlands.AllField.LocalFactor

universe uF

variable (F : Type uF) [Field F]

/-- The unit `q⁻¹` for the canonical residue cardinality `q`: the reflection
`X ↦ q⁻¹ / X` corresponds to `s ↦ 1 - s` at `X = q^(-s)`. -/
def residueReflection [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : ℂˣ :=
  WeilDeligne.reflectionScale ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ)
    (by exact_mod_cast Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one)

@[simp]
theorem coe_residueReflection [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    (residueReflection F : ℂ) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ)⁻¹ := by
  simp [residueReflection]

end Langlands.AllField.LocalFactor
