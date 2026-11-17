# A finite Galois action with prescribed Frobenius

Author: Worker 187.

Let `k : Type u` be a finite field and let `θ` be a finite-order
element of any group in universe `v`. `FiniteFrobeniusAction k θ`
records an extension `K : Type u`, its field and `k`-algebra
structures, finiteness and finite Galois properties, a homomorphism
`Gal(K/k) → A` sending arithmetic Frobenius to `θ`, and the equality
`[K:k] = orderOf θ`.

`finiteFrobeniusAction` constructs these data. Mathlib's chosen
finite-field extension of degree `orderOf θ` exists because that
order is positive. An `ULift` places this extension in the same
universe as `k`; it preserves the degree. Frobenius generates its
Galois group and has order equal to the degree. Mathlib's
`monoidHomOfForallMemZpowers` therefore constructs the homomorphism
with the prescribed generator image.

The provenance is an internal adapter derived from the imported
Mathlib extension, Frobenius, cyclic-group, and universe-lift
constructions. No finiteness of the target group is assumed.
