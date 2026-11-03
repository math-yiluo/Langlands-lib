# Principal open subsets of complex character tori

Author: Worker 34.

This is a derived topological and polynomial unit. It defines the principal open
locus `complexTorusPrincipalOpen p` by evaluating a complex multivariate polynomial
on the underlying complex values of a tuple of complex units. The torus is the
multiplicative complex torus, equipped with its usual product topology.

The nonvanishing locus is open by continuity of polynomial evaluation. For a
finite variable type and a nonzero polynomial, its nonvanishing locus in affine
space is dense: otherwise the polynomial vanishes on a nonempty open box. Each
side of the box is infinite, since complex numbers have nontrivial punctured
neighborhoods. `MvPolynomial.funext_set` then makes the polynomial zero. The
coordinatewise inclusion of complex units into complex numbers is open, so the
preimage of the dense affine locus is dense in the torus. The argument includes
the empty variable type and makes no positive-rank assumption.

The polynomial variable type has an arbitrary universe. Openness requires no
finiteness hypothesis; the density statements assume that this type is finite.
`complexTorusPrincipalOpen_finsetProd` identifies a finite intersection with
the nonvanishing locus of the product, and
`dense_iInter_complexTorusPrincipalOpen` derives density when every selected
polynomial is nonzero. The indexing type of this finite family has its own
universe, and the empty family is included.

The `_preimage` lemmas transport openness and density along an explicitly given
homeomorphism from any topological space to the same complex torus.
`dense_of_complexTorusPrincipalOpen_preimage_subset` makes the remaining
application condition explicit: a subset containing that coordinate principal
open locus is dense. No algebraic geometry structure, generic irreducibility or
unproved density input is included in the homeomorphism or polynomial condition.

The implemented dependencies are the pinned Mathlib polynomial extensionality,
continuity, punctured-neighborhood, open-map and topological-density lemmas.
There are no project-module dependencies or claims attributed to original
representation-theoretic literature.

This unit supplies no representation-theoretic genericity or comparison theorem.
The host rational exact finite-length K0 Weyl-conjugacy proposition remains open.
