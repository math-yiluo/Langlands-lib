# Finite-place Artin characters of a rational principal idele at level p^k

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalAwayProduct`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Fix a prime `p`, an exponent `k ≥ 0` and `x : ℚˣ`. For each finite place of `ℚ` the file takes the library's chosen finite-place Artin symbol of the principal idele of `x` in the rational cyclotomic field of level `p ^ k` and reads it in `(ZMod (p ^ k))ˣ` through `IsCyclotomicExtension.Rat.galEquivZMod`. It computes these characters prime by prime and writes their product over all finite places as the factor at `p` times an explicit finite product over the other primes dividing `x`.

## Main definitions and results

- `rationalCyclotomicPrincipalHeightOneCharacter p k x v`: the character at a height-one prime `v` of `𝓞 ℚ`; `rationalCyclotomicPrincipalFinitePlaceCharacter p k x q` is the same, indexed by `q : Nat.Primes` through `Rat.HeightOneSpectrum.primesEquiv`. The `..._spec` lemmas unfold them.
- `rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime_succ_formula`: at level `p ^ (n + 1)` the character at `p` is the reduction modulo `p ^ (n + 1)` of the unit `p ^ (−v_p(x)) · x` of `ℤ_[p]`.
- `rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne`: for `q ≠ p` the character at `q` is `q ^ (−v_q(x))` in `(ZMod (p ^ k))ˣ`; `rationalPrime_not_dvd_pow_of_ne` supplies `q ∤ p ^ k`.
- `..._eq_one_of_not_mem_support` and `rationalCyclotomicPrincipalFinitePlaceCharacters_hasFiniteMulSupport`: the character is trivial at primes outside `rationalPrimeFactorizationPrimeSupport x p`, so only finitely many are nontrivial.
- `rationalCyclotomicPrincipalAwayFinitePlaceCharacter_finprod_eq_factorizationProduct`: the product over `q ≠ p` equals the explicit product of `q ^ (−v_q(x))` over that support with `p` removed.
- `rationalPrimeUnitCharacter_mul_principalAwayFactorizationProduct_eq_sign`: the reduction modulo `p ^ k` of the `p`-unit part of `x`, times this explicit product, is the reduction of the sign unit `rationalSignPadicUnit x p`.
- `rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_finprod` and `..._prime_mul_factorizationProduct`: the product over all height-one primes of the characters equals the character at `p` times the product over `q ≠ p`, respectively times the explicit product.

The formulas at `q ≠ p` and at `p` come from the unramified and the prime-power computations of the finite-place Artin symbol in rational cyclotomic fields; the product identities are reindexing of `finprod`, together with the prime factorisation of `x`.

## Remarks

- Only finite places occur; the archimedean factor is not treated here.
- `k = 0` is allowed, but the formula at `p` needs a positive exponent `n + 1`.
- The exponent `−v_q(x)` reflects the library's local reciprocity normalisation, in which a prime element has normalised valuation `−1`.
- The support is the bounded set of primes used by `rationalPrimeFactorizationPrimeSupport`, which may contain primes not dividing `x`; their factors are `1`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalCyclotomicPrincipalAwayProduct.lean`: the Lean file is the source byte for byte (SHA-256 `74f12c2227eef495849cdd60180036f2d9bd87d1b533711ed8e359cc81c3a5af`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
