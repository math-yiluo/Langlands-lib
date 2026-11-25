# The Eisenstein polynomial of the p-power cyclotomic extension of ℚ_p

Module `Nyll.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinPolynomial`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file studies `ℚ_[p](ζ)` for a primitive `p^(k+1)`-th root of unity `ζ`, through the translated cyclotomic polynomial `Φ(X + 1)`, where `Φ` is the cyclotomic polynomial of index `p^(k+1)`. It transports the Eisenstein property of that polynomial from ℤ to `ℤ_[p]`, deduces irreducibility of `Φ` over `ℚ_[p]`, and from it the degree, the Galois group and the norm of `1 − ζ`.

## Main results

Throughout, `p` is prime, `L` is a field over `ℚ_[p]`, `ζ ∈ L` is a primitive `p^(k+1)`-th root of unity and `hgen` says that `ζ` generates `L` as a `ℚ_[p]`-algebra.

- `padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k`: the polynomial `Φ(X + 1)` over `ℤ_[p]`; `..._isEisensteinAt` shows it is Eisenstein at `(p)`, and `..._irreducible` that it is irreducible over `ℤ_[p]`.
- `padicCyclotomicTotallyRamifiedShiftedCyclotomicPadic_irreducible` and `padicCyclotomicPolynomial_irreducible_prime_pow_succ`: irreducibility over `ℚ_[p]` of the translate and of `Φ` itself, by Gauss's lemma and the substitution `X ↦ X − 1`.
- `padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top`: under `hgen`, `L` is a `p^(k+1)`-cyclotomic extension of `ℚ_[p]` in Mathlib's sense.
- `padicCyclotomicTotallyRamified_finrank_eq_totient`, `padicCyclotomic_finrank_eq_prime_sub_one_mul_pow`: `[L : ℚ_[p]] = φ(p^(k+1)) = (p − 1)p^k`.
- `padicCyclotomicTotallyRamified_galoisGroupEquivUnits`: `Gal(L/ℚ_[p]) ≃* (ℤ/p^(k+1))ˣ`.
- `padicCyclotomic_norm_one_sub_primitiveRoot_eq_prime`: `Algebra.norm ℚ_[p] (1 − ζ) = p`, including the case `p^(k+1) = 2`, treated separately.
- `padicCyclotomicTotallyRamified_minpoly_sub_one_padicInt`: the minimal polynomial of `ζ − 1` over `ℤ_[p]` is the Eisenstein translate.
- Also: `ζ` is integral over `ℤ_[p]` (`hgen` is not needed for this), and, for commutative rings `R` and `A` with `A` a finite free `R`-algebra, `Algebra.norm R x` is a unit if and only if `x` is (`padicCyclotomicTotallyRamified_norm_isUnit_iff`).

The degree, Galois group and norm come from Mathlib's results on cyclotomic extensions once irreducibility over `ℚ_[p]` is known.

## Watch for

- The module comment says the file proves that the extension is totally ramified, that its valuation ring is `ℤ_[p][ζ]`, and that `1 − ζ` is a prime element. None of these is proved in this file: it proves Eisenstein-ness, irreducibility, the degree, the Galois group, the norm of `1 − ζ` and the minimal polynomial of `ζ − 1`. Docstrings label results as parts (i), (ii) and (iv) of a "totally ramified cyclotomic theorem"; part (iii) does not appear here.
- The exponent is written `k + 1`, so `k = 0` means `ζ` of order `p`.
- The `ℤ_[p]`-algebra structure on `L` is a local instance, through `ℚ_[p]`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Padic/Cyclotomic/TotallyRamified/EisensteinPolynomial.lean`: the Lean file is the source byte for byte (SHA-256 `f17b7f0b9a73d04de9a02217f863dcb1522d8ba99cd0eef84091bb240d106e7d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
