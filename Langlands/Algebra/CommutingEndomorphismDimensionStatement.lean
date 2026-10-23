import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Basic.Complex.Basic

/-! A natural-power form of the commuting endomorphism algebra dimension bound. -/

namespace Langlands

universe uV

/-- BZ76 Lemma 4.10, with real exponents cleared by a positive natural power.
The zero-generator and zero-dimensional cases are included. -/
def CommutingEndomorphismDimensionStatement : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ) (a : Fin l → Module.End ℂ V),
    (∀ i j, Commute (a i) (a j)) →
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ^ (2 ^ l) ≤
      Module.finrank ℂ V ^ (2 ^ (l + 1) - 2)

end Langlands
