# Affine Frobenius image quotients and coordinate powers

For an affine group scheme of finite type over an algebraically closed field,
`FrobeniusImageQuotientStatement` applies to any finite-coordinate matrix
representation. The representation followed by matrix Frobenius factors through
a schematically dominant fppf quotient by its full scheme kernel and a closed
subgroup of the same general linear group. In the actual affine coordinate
algebras, every function pulled back along the quotient is a characteristic
power.

`frobeniusImageQuotient` uses the published affine homomorphism image theorem
for the fppf factorization. A closed immersion of affine schemes has surjective
coordinate pullback, so each image function pulls back from a function on the
general linear group. On the explicit coordinate ring of that group, the
Frobenius map raises the matrix entries and inverse entries to the characteristic
power. Field scalars also admit roots. Polynomial induction gives the power
formula for all regular functions. The affine point equivalence and naturality
of the coordinate evaluation transfer this calculation to the actual schemes.
The quotient's flatness and surjectivity give schematic dominance.

This is a derived step for induction in the connected necessity of Nagata's
theorem. It keeps the full kernel on all scheme tests and allows nonreduced
source and image groups.
