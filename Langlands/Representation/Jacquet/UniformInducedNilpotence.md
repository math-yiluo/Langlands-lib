# Uniform nilpotence on fixed levels of unramified induced Jacquet families

This internal supporting module bounds generalized-eigenvector nilpotence orders
at a fixed compact-open level uniformly over all unramified twists of an actual
normalized induced representation. The parameter need not be unitary. The group
and representation carrier universes remain independent.

`inducedFixedNilpotenceOrder` is the dimension of the fixed vectors at the given
level in the untwisted normalized induction. A compact-representative subgroup
makes the inducing quotient compact. Source admissibility gives admissibility of
the untwisted induction. Continuous unramified characters are trivial on compact
subgroups after inflation through the continuous Levi projection, so the
published fixed-vector equivalence identifies every twisted induced fixed space
with that one untwisted space.

For a second literal triple consisting of the Jacquet radical, its normalizing
Levi, and opposite subgroup, the supplied Iwahori contraction at the fixed level
makes the actual quotient map onto the unnormalized Jacquet fixed space
surjective. The published normalized-fixed-vector equivalence on the compact
intersection identifies this with the actual normalized Jacquet fixed space.
Its dimension is therefore bounded by the untwisted induced fixed dimension.

A central component preserves that Jacquet fixed space. Kernel stabilization on
a finite-dimensional space makes every simultaneous generalized eigenvector at
that level annihilated by each character linear factor raised to this common
dimension bound. The proof restricts the linear factor to the fixed space, uses
the published finite-dimensional kernel stabilization theorem, and raises the
power to the stated dimension bound.

This is derived infrastructure for the fixed multiplicities in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*
(2003), source `waldspurger-2003-plancherel`, I.3 and I.5 and the uniform exponent
polynomials in the proofs of VI.2.1 and VI.2.3, printed pp.297–300. The actual
standard-group contraction and common level for the orbit coefficient vectors
remain to be instantiated by the decay proof. No exponent contraction or
coefficient estimate is assumed or proved here, and this is not the principal
positive-decay theorem.
