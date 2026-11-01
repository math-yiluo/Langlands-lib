# Finite Frobenius maps on finite type integer algebras

`finiteIterateFrobenius` proves exactly `FiniteIterateFrobeniusStatement`
at arbitrary universe, using the elementwise helper `finite_iterateFrobenius`.

`finite_iterateFrobenius` says that every iterate of Frobenius on a
commutative finite type integer algebra is a finite ring homomorphism.
Its exponential-characteristic parameter also permits characteristic zero,
where that parameter is one and the map is the identity.

The proof is an internal derivation from Mathlib's integral and finite type
map criteria. An element `x` satisfies the monic polynomial
`X^(p^n) - C x` when evaluated through the iterated Frobenius map.
Every integer is fixed by a unital ring endomorphism, so the composite of
the integer map and Frobenius is the original finite type integer map.
Finite type descends to the second factor, and an integral finite type
ring map is finite.

This lemma supplies only a Frobenius finiteness tool. It asserts no
normalization theorem.
