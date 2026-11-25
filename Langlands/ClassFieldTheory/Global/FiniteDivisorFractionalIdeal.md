# Finite divisors and nonzero fractional ideals

This module constructs the actual prime-product equivalence
`finiteDivisorFractionalIdealEquiv` from multiplicatively tagged
`FinitePlaceDivisor E` to units of the fractional-ideal monoid of `𝓞 E`.
It applies to every number field in arbitrary universe. The forward map is
the finitely supported product of prime fractional ideals raised to integer
exponents; the inverse records `FractionalIdeal.count` at every finite prime.
Negative exponents are included. Both inverse identities, the single-prime
formula and homomorphism laws are supplied.

This is a derived factorization adapter for the idele-to-ideal map in Milne,
*Class Field Theory* v4.03, Chapter V §4.1, printed p.170/PDF179; registered
source `milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
It does not construct an idele map, a class-group map, or any Galois action.

The proof uses Mathlib Dedekind factorization directly. Finite support of the
inverse is `FractionalIdeal.finite_factors`. Injectivity follows by comparing
the prime products in `finprod_heightOneSpectrum_factorization'`.
`count_finsuppProd` proves that the divisor of the constructed product is
the original divisor. This and injectivity prove both inverse identities.
The multiplication law for divisors is `count_mul`; injectivity transfers it
to the prime-product construction. `Units.mk0` packages the nonzero product
as an actual unit; `Finsupp.prod_single_index` gives the single-prime formula.
