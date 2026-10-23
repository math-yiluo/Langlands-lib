import Langlands.Global.ProfiniteIntegerRing
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! # Normalized comparison of residue families with the product of p-adic integers -/

namespace Langlands.Global

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The residue-limit ring is topologically ring-isomorphic to the actual product
of p-adic integer rings, compatibly with the canonical integer maps.
This proposition is a statement target, not a chosen equivalence. -/
def ProfiniteIntegerPadicProductComparison : Prop :=
  ∃ e : ProfiniteIntegerRing ≃+* ((p : Nat.Primes) → PadicInt (p : ℕ)),
    Continuous e ∧ Continuous e.symm ∧
      ∀ (z : ℤ) (p : Nat.Primes),
        e (ProfiniteIntegerRing.intCastHom z) p = (z : PadicInt (p : ℕ))

end Langlands.Global
