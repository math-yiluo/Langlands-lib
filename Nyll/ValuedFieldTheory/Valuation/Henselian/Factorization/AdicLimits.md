# Coefficientwise adic limits of polynomial approximations

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.AdicLimits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a commutative ring `R` with an ideal `I`, the file prepares the limit step of the approximation proof of Hensel's lemma: sequences of polynomials of bounded degree whose coefficients converge `I`-adically have polynomial limits, and limits of approximate factorizations are factorizations.

## Definitions and results

- `henselFactorization_adicCoeffCauchy I x`: for `M ≤ N`, `x N − x M ∈ I^(M+1)`. It implies Mathlib's `AdicCompletion.IsAdicCauchy`, and if `R` is `I`-adically precomplete, `x` has a limit `L` with `x n − L ∈ I^n` (`henselFactorization_exists_adicCoeffLimit`).
- `henselFactorization_polyOfLimitCoeffs N c`: the polynomial that is the sum of the `cᵢ Xⁱ` for `i ≤ N`, with lemmas on its coefficients and degree `≤ N`.
- `henselFactorization_exists_limitPolynomial_of_bounded_coeffLimits`: for `R` precomplete, a sequence of polynomials of degree `≤ N` whose coefficient sequences satisfy the Cauchy condition has a limit `P` of degree `≤ N`, with all coefficients of `Pₙ − P` in `I^n`.
- `henselFactorization_limit_factor_eq_of_approximants`: for `R` `I`-adically separated, if the coefficients of `f − Gₙ Hₙ`, `Gₙ − G` and `Hₙ − H` lie in `I^n` for all `n`, then `f = G · H`.
- `henselFactorization_limit_reduction_of_approx_reduction`: if every `Pₙ` is congruent to `P₀` modulo `I`, so is the limit.
- Helpers: coefficient ideals are stable under products and differences of products; a polynomial with coefficients in every `I^n` vanishes in a separated ring; coefficientwise congruence modulo a kernel, or modulo the maximal ideal of a local ring, gives equal reductions.

## Caveats

- The Cauchy condition is the library's own, with `I^(M+1)` in place of Mathlib's `I^M`; it is stronger than Mathlib's.
- Separatedness and precompleteness are assumed separately where each is needed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/AdicLimits.lean`: the Lean file is the source byte for byte (SHA-256 `4091e8eb0649f5d23a86cc23fb3d86d201c7591e3fdb38d228d471bef792692d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
