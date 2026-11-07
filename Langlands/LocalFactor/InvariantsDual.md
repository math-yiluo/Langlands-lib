# Duals of finite-inertia invariant spaces

This internal construction restricts inertia-invariant algebraic functionals
to the original invariant subspace. For a normal subgroup with finite image
in a representation over a characteristic-zero field, this restriction is a
representation equivalence. The coefficient, group and carrier universes are
independent; the algebraic dual carrier has the maximum of the coefficient
and original carrier universes. Rank zero is allowed.

The proof factors the inertia action through its finite kernel quotient and
uses Mathlib's `Representation.averageMap`. Its image is invariant, it fixes
invariants, and it is unchanged by precomposing an inertia operator. An
invariant functional has the same value on a vector and its average. Thus
restriction is injective, and composing any functional on the fixed subspace
with the averaging projection supplies a preimage. Restriction commutes with
the full ambient group action by normality; this proves the equivalence.

Conjugacy across that equivalence identifies the Euler polynomial of the
dual fixed space with the Euler polynomial of the transpose of the inverse
group operator on the original fixed space. The transpose determinant
identity gives the evaluation formula `det(1 - z A(g⁻¹)|V^I)`. The local
continuous specialization obtains finite inertia image from the published
`localWeilContinuity` theorem for the actual local Weil group.

The provenance is internal: this composes published representation invariants,
algebraic duals, the local continuity theorem, Mathlib's finite group averaging
and transpose determinant identity, and the published determinant definition
of the Euler polynomial. It supplies no local epsilon-system existence or
assembly inheritance proof.
