import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-! # Reducedness of finite commutative Hopf algebras in characteristic zero -/

universe u v

namespace Langlands

/-- The finite coordinate-algebra consequence of Cartier's characteristic-zero
smoothness theorem. -/
def FiniteHopfCharZeroReducedStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (H : Type v)
    [CommRing H] [HopfAlgebra k H], Module.Finite k H → IsReduced H

end Langlands
