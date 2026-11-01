import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.LocalField.Topology

/-! # The unit is an actual matrix rational value -/

noncomputable section

namespace Langlands.GodementJacquet

open RankinSelberg

universe uF uV

/-- Every nonzero smooth representation has actual matrix rational value `1`,
on both the original and inverse-transpose sides. -/
def MatrixUnitValueStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ n : ℕ,
      letI : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
      letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
        IsSmooth σ →
        (1 : RationalFunctions) ∈ Padic.matrixRationalValues F σ ∧
          (1 : RationalFunctions) ∈ Padic.iotaMatrixRationalValues F σ

end Langlands.GodementJacquet
