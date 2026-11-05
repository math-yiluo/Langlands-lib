# Frobenius approximation on finite sets

This internal lemma concerns an arbitrary algebraic extension `K/k` of a finite
field. For every `k`-automorphism of `K` and every finite set of elements of `K`,
`exists_frobenius_pow_eq_on_finset` supplies a nonnegative power of the actual
arithmetic Frobenius that agrees with the automorphism on that set.
The defined natural number `frobeniusApproximationExponent` chooses such an
exponent, and `frobeniusApproximationExponent_spec` gives its agreement property.
The exponent is chosen noncomputably; it is not asserted to be least or unique.

The proof adjoins the finite set to `k`. Algebraicity makes this intermediate
field finite dimensional, hence finite and Galois. Mathlib's finite-field
Frobenius generator theorem supplies a power giving the restricted automorphism.
The cardinality-power formula identifies its values with those of Frobenius on
`K`. No finite dimensionality or normality of `K/k` is assumed.

Worker 1611 derived this adapter from the imported Mathlib results.
