import Langlands.AlgebraicGeometry.Picard.MumfordRosatiEulerDegreeStatement
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiEulerDegreeAssembly

/-! # Proof of the Euler-degree formula for `n • λ + f^∨ λ f` -/

universe u

namespace Langlands.AbelianScheme.Rosati

/-- `MumfordEulerDegreeStatement` holds. -/
theorem mumfordEulerDegree : MumfordEulerDegreeStatement.{u} :=
  fun P k _ _ A W lam L B evaluationB M evaluation hL hlam f =>
    MumfordPicardClass.eulerDegree P k A W lam L B evaluationB M evaluation hL hlam f

end Langlands.AbelianScheme.Rosati
