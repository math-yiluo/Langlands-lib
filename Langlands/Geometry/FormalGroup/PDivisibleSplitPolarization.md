# The split p-divisible group with its tautological polarization

Given the finite Cartier exactness theorem, `PDivisibleGroup.splitWithDual`
constructs the product of a p-divisible group and its actual Cartier dual.
The inclusion on each product level is the original inclusion paired with
the dual of the original transfer. The transfer is the original transfer
paired with the dual of the original inclusion. Each factor is retained as
a finite group scheme at every level.

`PrincipalPolarization` records a perfect relative character pairing on
each finite level, alternating on every test scheme, with the two tower
arrows adjoint. `splitPrincipalPolarization` constructs it on the actual
product tower. Its evaluation on `(x, χ)` and `(y, ψ)` is
`ψ(x) * χ(y)⁻¹`. Perfectness follows from the finite split pairing
isomorphism. Adjointness follows by evaluating the original map against
the opposite dual map in each of the two factors.

This is the construction of the tautological polarization for the product
with the dual in Rapoport–Zink, *Period Spaces for p-divisible Groups*
(1996), §6.43, printed p. 309 (PDF p. 321), just before (6.17). The dual
transition maps are those of Tate, *p-Divisible Groups* (1967), §2.3,
printed p. 166 (PDF p. 5).
