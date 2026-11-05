import Langlands.Algebra.FiniteHopfCharZeroReducedStatement
import Langlands.Algebra.FiniteHopfCharZero

/-! # Proof of finite Hopf reducedness in characteristic zero -/

universe u v

namespace Langlands

/-- Every finite-dimensional commutative Hopf algebra over a characteristic-zero
field is reduced. -/
theorem finiteHopfCharZeroReduced :
    FiniteHopfCharZeroReducedStatement.{u, v} := by
  intro k _ _ H _ _ hfinite
  let : Module.Finite k H := hfinite
  exact FiniteHopfCharZero.isReduced (k := k) (H := H)

end Langlands
