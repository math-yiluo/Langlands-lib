# Prime factorization of a nonzero rational and its p-adic unit part

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalPrimeFactorization`, copied from the Lean library NYLL with one local instance replaced (see "Changed declarations"). The origin of the file is given at the end of this page.

This file sets up the elementary factorization of a nonzero rational number used in the calculation of principal ideles over `ℚ`. For `x : ℚˣ` and a prime `p`, dividing `x` by its `p`-power leaves a rational number of `p`-adic valuation zero, which equals the sign of `x` times the product of `q ^ v_q(x)` over the primes `q ≠ p`. The file then lifts this identity to units of `ℤ_[p]` and reduces it modulo `p ^ k`.

## Main definitions and results

- `rationalPrimeFactorizationSupport x p`: the primes below `max(|num x|, den x, p) + 1`, a finite set that contains `p` and every prime dividing the numerator or the denominator. `rationalPrimeFactorizationPrimeSupport` is the same set as a `Finset Nat.Primes`, with an equivalence between the two after erasing `p`.
- `rationalPrimeUnit x p`: the unit `p ^ (−v_p(x)) · x` of `ℚ`; `padicValRat_rationalPrimeUnit` says its `p`-adic valuation is zero.
- `rational_factorization_over_support`: `x = sign(num x) · ∏ q ^ v_q(x)` over the support; `rationalPrimeUnit_factorization`: the same with `p` erased, for `rationalPrimeUnit x p`.
- `padicIntUnitOfRat`: a nonzero rational of `p`-adic valuation zero as a unit of `ℤ_[p]`. `rationalSignPadicUnit x p`: the sign of `x` as such a unit, with square one. `padicNatUnit p q h`: a natural number `q` coprime to `p` as a unit of `ℤ_[p]`; its reduction modulo `p ^ k` is `ZMod.unitOfCoprime q`.
- `padicNatUnit_not_isOfFinOrder_of_one_lt`: for `n > 1` coprime to `p`, the unit `n` of `ℤ_[p]` has infinite order. `padicValRat_rationalPrime_succ`: `p + 1` has `p`-adic valuation zero.
- `padicIntUnitOfRat_rationalPrimeUnit_factorization`: in `ℤ_[p]ˣ`, the unit part of `x` equals the sign unit times the product of `padicNatUnit q ^ v_q(x)` over the support with `p` erased.
- `padicIntUnitOfRat_rationalPrimeUnit_toZModPow` and its variants: the same identity after reduction to `(ZMod (p ^ k))ˣ`, rearranged in several forms (multiplied by the inverse factors to leave the sign, multiplied by the sign to cancel it, inverse–cancellation form), one of them indexed by the prime-valued support.

## Proofs

The rational factorization comes from Mathlib's `Nat.prod_pow_prime_padicValNat` applied to the numerator and the denominator. The `ℤ_[p]` identity is checked after the injective map `ℤ_[p] → ℚ_[p]`, by mapping the rational identity into `ℚ_[p]`; the reductions modulo `p ^ k` apply `PadicInt.toZModPow`.

## Remarks

- The support is a bounded range of primes chosen for convenience, not the set of primes actually dividing `x`; primes outside the factorization contribute exponent zero.
- The sign is taken from the numerator, `Int.sign (num x)`.

## Changed declarations

The source declares the anonymous local instance `local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩` in namespace `GlobalClassFieldTheory.Reciprocity`. Lean names it from its type, and other modules of the copy declare the same name, so the modules could not be imported together. Here the declaration is replaced by `attribute [local instance] fact_prime_val`, where `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact p.1.Prime` (proof `⟨p.2⟩`, module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`, imported with `public import`) has the same type and proof. The instance stays local to the file; no statement or proof of the file changes otherwise.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalPrimeFactorization.lean`. The Lean file is the source byte for byte except for the change above (SHA-256 of the source: `e9c9ae49b330259a395ff00d4e703508bd8778dd68a37b64bf5aa94dc6f02da5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
