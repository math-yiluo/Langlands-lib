import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement

/-! # The quotient map to the bundled opposite Jacquet module -/

noncomputable section

universe uF uV

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- The opposite coinvariant map, with the bundled opposite Jacquet module as target. -/
def oppositeJacquetMk (C : BlockShape n) (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    A →ₗ[ℂ] CuspidalJacquetMultiplicity.oppositeJacquet T C A :=
  Jacquet.mk A.ρ (C.oppositeUnipotentSubgroup F.Carrier)

end Langlands.PadicField.TopologicalData
