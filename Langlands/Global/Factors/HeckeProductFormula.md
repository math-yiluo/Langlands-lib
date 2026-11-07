# Actual additive product formulas on the adeles and the diagonal

This internal derived module proves finite-coordinate control for continuous
characters on arbitrary products, and uses it on the actual adelic integral
product. A character whose value lies in a sufficiently small neighborhood of
one on every positive power must be trivial. Continuity at the identity gives a
finite list of coordinates on which an identity neighborhood depends. Therefore
the entire subgroup with those coordinates equal to the identity lies in the
kernel, even when infinitely many other coordinates are nontrivial. Both the
circle-valued additive and arbitrary complex unit-valued multiplicative versions
are proved, with no compactness assumption.

`additiveIntegralControl` selects such a finite list for the restriction of a
global additive character to the full product of completed integer rings.
`nonintegralPlaces` records exactly the finitely many nonintegral coordinates of
a finite adele. `finiteAdditivePartialSum` inserts any chosen finite set of its
actual coordinates, with zero elsewhere.

`finite_additive_product` applies to every finite set containing the character's
integral control and the adele's nonintegral places. The remaining coordinates
form an actual element of the integral product with zero controlled coordinates,
so its character value is one. The sum of this remainder and the finite partial
sum equals the original finite adele, proving the finite product formula with
the published actual restrictions. The result does not require self-duality or
diagonal triviality. The coordinate proofs explicitly apply the ring projections
to the finite sum and evaluate the actual single-coordinate inclusions.

`infinite_additive_sum` reconstructs the archimedean part as the sum of the
single-coordinate inclusions over all infinite places. Applying the additive
character gives `infinite_additive_product`. Splitting a full adele into its
archimedean and finite parts then gives `additive_product`:

$$
\psi(x)=
\left(\prod_{v\mid\infty}\psi_v(x_v)\right)
\left(\prod_{v\in S}\psi_v(x_v)\right).
$$

Here the factors are exactly `infiniteAdditiveRestriction` and
`finiteAdditiveRestriction`, and the finite set contains both
`additiveIntegralControl ψ` and `nonintegralPlaces x.2`. No infinite product or
convergence assertion occurs. The whole integral remainder is in the kernel,
which is stronger than triviality on its individual single-coordinate factors.

`diagonal_additive_product` substitutes the actual diagonal image of an element
of the original number field. Under the explicit hypothesis that the global
character is trivial on every diagonal element, the displayed local product
equals one. Each coordinate is the corresponding actual `algebraMap` into the
completion. The number field remains in an unrestricted universe. The argument
does not change the additive character, insert a Fourier sign, or impose
archimedean scale or Haar-measure conventions.

The provenance is internal: the direct continuity and small-subgroup argument
followed by coordinatewise identities in Mathlib's actual restricted product and
finite archimedean product. These are helper definitions and proved identities
for the global Hecke task. The generic multiplicative kernel lemma is included
as support for the analogous multiplicative construction, which is not asserted
here. The module does not prove adelic self-duality, local Fourier identities,
Euler-product continuation, or the global functional equation.
