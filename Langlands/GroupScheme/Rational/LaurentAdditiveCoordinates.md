# Additive-polynomial coordinates for pointed Laurent functions

This internal construction continues `LaurentFrobeniusBasis`. Let `k` be
any commutative ring, `p` a prime, and `I` an arbitrary index type, with
the coefficient and index universes independent. The linear map
`additiveEncoding` sends the coefficient basis vector
`X^((p^r) • m) - 1` to `Y_m^(p^r)`, with one polynomial variable for every
nonzero integer character `m : I → ℤ` not divisible by `p`.
When `k` has characteristic `p`, this input vector also equals
`(X^m - 1)^(p^r)`.

The exponents `single m (p^r)` are pairwise distinct: equality forces the
same character and then the same exponent because `p ≥ 2`. The map on
finitely supported coefficients is therefore injective, and the two
coefficient-basis equivalences give injectivity of `additiveEncoding`.

Under the additional assumption `CharP k p`, `frobeniusMap` is the
semilinear Frobenius endomorphism of the augmentation kernel.
It advances the orbit index by one. Checking on the coefficient
basis proves that `additiveEncoding` commutes with this endomorphism and
ordinary polynomial Frobenius. This comparison uses no perfectness
assumption on the coefficient ring.

The map is a linear encoding for the Frobenius-module argument; the Lean
declaration makes no claim that it preserves multiplication. The
construction is derived from the preceding two Laurent modules and
Mathlib's polynomial coefficient and semilinear Frobenius APIs.
