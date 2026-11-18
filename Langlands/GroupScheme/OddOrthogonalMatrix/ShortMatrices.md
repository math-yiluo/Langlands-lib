# Polynomial unipotent matrices for the odd split form

For each signed hyperbolic coordinate `a`, this module constructs the
polynomial family acting on rows by

- `z ↦ z + t * x(a.swap)`;
- `x(a) ↦ x(a) - 2*t*z - t²*x(a.swap)`;
- every other hyperbolic coordinate stays fixed.

The matrices are defined over every commutative coefficient ring. Direct
matrix multiplication proves the additive parameter law, giving a
homomorphism from the additive parameter group (written using
`Multiplicative`) to matrix units. Its paired-coordinate to axis entry
is the parameter, so the homomorphism is injective over every coefficient
ring. Factoring each matrix as three elementary
transvections proves determinant one. Expanding the displayed coordinate
change proves preservation of the entire polynomial `z² + ∑ᵢ xᵢyᵢ`.
The formulas commute with all coefficient-ring homomorphisms.

This is an internal explicit-matrix construction derived from the split odd
quadratic polynomial. The name `shortMatrix` anticipates its role in the
short-root subgroups. This module proves the polynomial and group identities;
it does not yet identify these families with roots of a reductive group.
