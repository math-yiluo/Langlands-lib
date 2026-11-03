# The actual kernel of a split-torus character is diagonalizable

This internal construction identifies the actual scheme-theoretic kernel of a
character `a` of a split torus `T` over a commutative domain `k` with
`D(X*(T)/ℤa)`. The universe is arbitrary. The relation is the full subgroup of
integer multiples of `a`; it is not saturated. No nonzero or primitivity
hypothesis on `a` is needed, and the quotient may have torsion in the
characteristic. No smoothness of the kernel is assumed or concluded.

`characterLattice.pointCharacters` evaluates actual torus points on characters,
with values in global units of an arbitrary test scheme. The implementation
chooses a split-torus isomorphism, identifies its character lattice with
`ℤ^I`, and applies the finite product formula for character evaluation.
This proves that the intrinsic evaluation is bijective. The resulting
`pointCharactersEquiv` is natural under all refinements of the test scheme.

`Diagonalizable.kernelCharacterPointsEquiv` combines this evaluation with the
existing actual kernel point equivalence. Its point model is the group of
lattice characters which kill `a`. The quotient-character universal property
identifies the same group with the points of `D(X*(T)/ℤa)`. Both identifications
are natural on every test scheme. `kernelDiagonalizableIso` is the resulting
actual group-scheme isomorphism, obtained by the existing point-model
construction. `kernelDiagonalizableIso_inv` states its compatibility with
character evaluation: after the kernel inclusion, a character `b` evaluates
as the quotient character at the class of `b`.

`quotientLattice_fg` proves that the quotient lattice is finitely generated.
The proof transports finite generation from `ℤ^I` to the character lattice
and then uses the quotient instance. It retains all quotient torsion.

All content here is internally derived from the existing split-torus lattice,
scheme-kernel, corepresentation and quotient-character constructions. These
are construction and compatibility lemmas for the kernel-centralizer proof;
they do not establish representability or smoothness of the centralizer or
the reverse Lie-weight inclusion.
