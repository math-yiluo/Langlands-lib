import Langlands.Global.Arithmetic.FieldRealizationProof
import Langlands.Global.Arithmetic.SplitAuxiliaryQuadraticsProof

/-! # Field realization and split auxiliary quadratic fields -/

universe u v

namespace Langlands.Global

/-- Totally real Galois realization together with the split auxiliary
quadratic fields. -/
theorem fieldRealization : FieldRealizationStatement.{u, v} :=
  ⟨totallyRealGaloisRealization.{u, v}, splitAuxiliaryQuadratics.{u}⟩

end Langlands.Global
