# Normalization over finite fields

This private helper is Worker 706's finite-field contribution to the finite
normalization task.

`finite_normalization_of_normal_finite_subbase` treats a domain finite over
an injective normal noetherian subbase of finite type over the integers.
The fraction fields form a finite extension. The preceding bounded-Frobenius
helper makes the subbase's integral closure in the larger fraction field
finite. Transitivity of integrality embeds the domain's normalization
linearly into this finite module. Noetherianity and then extension of scalars
give the desired finite module over the domain.

`finite_normalization_of_finite_field` requires only that the domain be of
finite type over a finite field. Mathlib's Noether normalization supplies a
finite injective polynomial subbase. A polynomial ring in finitely many
variables over a field is noetherian and a unique factorization domain,
hence integrally closed. The coefficient field is finite over the integers,
so the polynomial subbase is of finite type over the integers. The preceding
theorem therefore applies without a separability condition.

`finite_normalization_of_prime_characteristic` installs the canonical algebra
over `ZMod p` for an integer finite type domain of prime characteristic `p`.
Finite type passes from the integers to this prime field by restriction of
scalars, so the finite-field result applies.

These are internal derivations from Mathlib's
`exists_finite_inj_algHom_of_fg`, unique factorization and localization
theorems, and the bounded-Frobenius helper explained in its paired Markdown.
They cover arbitrary universe and dimension. The characteristic-zero part
of the original task remains separate.
