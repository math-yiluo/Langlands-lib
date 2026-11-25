# Prime factorization of fractional ideals

Module `Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The group of nonzero fractional ideals of a number field `K` is identified with the free abelian group on the finite primes, written multiplicatively: an ideal `I` corresponds to its exponent vector `(ord_v I)_v`. Everything is built from Mathlib's `FractionalIdeal.count` and its unique factorization theorems.

## Main definitions and results

All declarations are in the namespace `NumberFieldFractionalIdealGroup`.

- `primePowerHom v`: the homomorphism `n ↦ 𝔭_v^n` from `Multiplicative ℤ` to the group of nonzero fractional ideals.
- `factorization`: the homomorphism from `Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ)` sending an exponent vector `(n_v)` to the product over `v` of `𝔭_v` raised to the power `n_v`; `factorization_val` writes this product at the level of fractional ideals.
- `finite_count_support` and `countVector I`: the exponents `FractionalIdeal.count K v I` of a nonzero fractional ideal vanish for all but finitely many `v`, so they form a finitely supported vector; `countVector_apply` evaluates it.
- `count_factorization`: the exponent at `v` of `factorization e` is `e v`.
- `ext_count`: two nonzero fractional ideals with the same exponent at every finite prime are equal.
- `factorization_injective`, `factorization_surjective` and `factorizationEquiv`: `factorization` is bijective, hence a multiplicative isomorphism.

## Proofs

`count_factorization` comes from Mathlib's `FractionalIdeal.count_finsuppProd`; `ext_count` from the factorization of a nonzero fractional ideal as a finite product of prime powers (`FractionalIdeal.finprod_heightOneSpectrum_factorization'`). Injectivity follows from `count_factorization`, and surjectivity from `ext_count` applied to `countVector I`.

## Points to watch

The statements are made for the ring of integers of a number field, although the Mathlib results they use are stated for Dedekind domains. The exponent vectors are wrapped in `Multiplicative`, so the isomorphism is between multiplicative groups.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/NumberFieldFractionalIdealFactorization.lean`: the Lean file is the source byte for byte (SHA-256 `07c41e3a19e1f808fa6f9b2e0dcdd2de31f236b20f068e86415e491e48de1482`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
