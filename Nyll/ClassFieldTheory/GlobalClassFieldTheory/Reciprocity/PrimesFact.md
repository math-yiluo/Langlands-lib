# The primality of a member of `Nat.Primes`, as a `Fact`

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`. It is not a file of the Lean library NYLL: it belongs to this copy, and holds one declaration shared by eight reciprocity files of the copy.

## Main definitions and results

- `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact (Nat.Prime p.val)`: the value of a member of Mathlib's `Nat.Primes` (the subtype `{p : ℕ // p.Prime}`) is prime, packaged as a `Fact`, so that it can serve as an instance.

It is a theorem, not a global instance. The files `CyclotomicPrincipalIdele`, `FinitePlaceCyclotomicFrobeniusLift`, `RationalCyclotomicCharacterRigidity`, `RationalCyclotomicFinitePlace`, `RationalCyclotomicPrincipalProduct`, `RationalCyclotomicZHatRigidity`, `RationalPrimeFactorization` and `RationalPrincipalLocalUnit` of this directory install it with `attribute [local instance] fact_prime_val`, in place of the anonymous local instance of the same type and proof that each of them declares in NYLL (see "Changed declarations" on their pages).

## Proofs

The proof is the membership proof of the subtype: `⟨p.2⟩`.

## Literature

None: the statement is the definition of `Nat.Primes`.
