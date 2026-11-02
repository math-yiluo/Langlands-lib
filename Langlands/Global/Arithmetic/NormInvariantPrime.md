# Uniqueness of a prime cut out by an invariant norm

Let `L/K` be a finite Galois extension of number fields, let `E` be a
nontrivially normed field, and let `j : L →+* E`. Suppose that a nonzero prime
`P` of the ring of integers of `L` is characterized by
`a ∈ P` if and only if `‖j a‖ < 1`. If `‖j (σ x)‖ = ‖j x‖` for every
`K`-automorphism `σ` of `L` and every `x : L`, then `P` is the unique nonzero
prime above any specified nonzero prime `v` of `K` over which `P` lies.
The fields `K`, `L` and `E` have independent universes.

The proof uses Mathlib's transitivity of the Galois action on primes above
`v`. Every such prime is `σ • P`. Membership in this ideal is membership of
`σ⁻¹ • a` in `P`, and the norm characterization and invariance show that
this is equivalent to membership of `a` in `P`. Equality of the underlying
ideals gives equality in `HeightOneSpectrum`.

The definition `normInvariantPrimeFiberUnique` packages this result as a
`Unique` structure on the type of nonzero primes above `v`, with distinguished
element `P`. Its uniqueness proof is `prime_unique_of_norm_invariant`.

This is an internal derived helper for the global realization construction.
It uses the standard Galois action on rings of integers and Mathlib's
`Ideal.exists_smul_eq_of_isGaloisGroup`; it asserts no completion comparison
or global realization on its own.
