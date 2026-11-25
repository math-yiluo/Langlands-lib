module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# The primality of a member of `Nat.Primes`, as a `Fact`

`fact_prime_val p` states that the value of `p : Nat.Primes` is prime, packaged as `Fact p.1.Prime`.
The reciprocity files that need this fact for every `p : Nat.Primes` install it with
`attribute [local instance] fact_prime_val`; it is not a global instance.
-/

@[expose] public section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- The value of a member of `Nat.Primes` is prime, as a `Fact`. -/
theorem fact_prime_val (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

end Reciprocity
end GlobalClassFieldTheory
