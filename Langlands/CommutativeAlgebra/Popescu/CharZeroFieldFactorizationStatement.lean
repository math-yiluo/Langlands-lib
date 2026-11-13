import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.Algebra.CharZero.Defs

/-! # Field extensions in characteristic zero have smooth factorizations -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemmas 10.158.11 (07BV) and 10.127.4 (07C3) with Proposition 10.158.9 (0322),
in characteristic zero: for a field extension `L / K` with `K` of characteristic zero,
every `K`-algebra map from a finitely presented `K`-algebra to `L` factors through a
smooth `K`-algebra. -/
def CharZeroFieldFactorizationStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [CharZero K] [Algebra K L],
    HasSmoothFactorizations K L

end Langlands.CommutativeAlgebra.Popescu
