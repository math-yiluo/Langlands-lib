# Free and finite factors of diagonalizable group schemes

This internal construction lifts the finitely generated abelian group structure
theorem to actual diagonalizable group schemes over any commutative base ring.
It retains the entire finite character factor, including torsion in the
characteristic and the nilpotents it can produce. No smoothness, connectedness
or reducedness of that finite factor is claimed.

`productCharactersEquiv` identifies characters of an abelian product with pairs
of characters. Restriction to the two inclusions is the forward map; multiplying
the two character values gives its inverse. `congrIso` transports an additive
isomorphism of character groups to an actual group-scheme isomorphism, with
`congrIso_hom` recording its evaluation on every test scheme.
`productIso` identifies the diagonalizable group of a product character group
with the actual categorical product of the two diagonalizable groups. Both
isomorphisms use the published character point equivalence on every test scheme,
prove naturality under every test-scheme morphism, and apply `isoOfPointModels`.

`splitFiniteIso` combines these isomorphisms with the published free-lattice
split-torus model. `exists_splitFiniteIso` applies Mathlib's
`AddCommGroup.equiv_free_prod_directSum_zmod` and transports its finite direct sum
and free coordinates into the original universe. It constructs a group-scheme
isomorphism `D(Λ) ≅ Gm^I × D(A)` for a finite index set `I` and finite abelian group
`A`. The `isFinite` instance proves that `D(A)` is finite over the original base:
its group algebra is a finite module because its monomial basis is indexed by
`A`, and the finite-algebra/spectrum equivalence supplies the morphism property.

The provenance is internal, from the existing diagonalizable character models,
actual product point equivalence and Mathlib's proved abelian group structure
theorem. The result does not produce reduced components or rational points of
the finite factor, select a dominating component, or prove unipotent splitness
or maximal-torus conjugacy.
