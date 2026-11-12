# The rational character lattice is free of finite rank

Author: Worker 3798 (Task 3798, `6d0882ee-6e45-410c-b5a1-86d4544a4ffb`).

`Langlands.GroupScheme.rationalCharacterLattice` proves exactly the
published proposition `Langlands.GroupScheme.RationalCharacterLatticeStatement.{u}`
(module [`CharactersStatement`](CharactersStatement.md)), at every universe `u`,
with no hypotheses.

For every field `k : Type u` and every connected reductive group scheme `G`
over `Spec k` (`IsConnectedReductive G`), the group `rationalCharacters G` of
rational characters is a free `ℤ`-module (`Module.Free ℤ`) and a finitely
generated `ℤ`-module (`Module.Finite ℤ`). The statement asserts both
properties, so finite generation is not replaced by freeness alone. The field
is arbitrary: no perfectness, characteristic, splitness or local-field
hypothesis is added.

## Implemented proof

The Lean module imports the existing proof `rationalCharacterLattice.{u}`.
The independently reviewed alias is consolidated into that declaration.

`Langlands.GroupScheme.rationalCharacterLattice`, from
[`CharacterLatticeProof`](CharacterLatticeProof.md), is a theorem already in the
Library with type `RationalCharacterLatticeStatement.{u}`. It was published in
the previous project instance, so this instance has no accepted artifact for
it. The accepted contribution for Task 3798 restaged the same proof. Integration
keeps the existing declaration and this import module with its explanation;
it adds no mathematics.

The Markdown of `CharacterLatticeProof` describes that proof. It uses only
that `G` is smooth, affine and connected over `Spec k`. The coordinate algebra
`O(G)` is then a finitely generated `k`-domain. Distinct characters give
`k`-linearly independent units of `O(G)`. The commutative algebra of
`CharacterLatticeAlgebra`, applied in the fraction field of `O(G)`, then shows
that the character group is free of finite rank over `ℤ`.

## Relation to the literature

The statement corresponds to Renard V.2.2 (see the statement's Markdown, which
explains that the arbitrary-field formulation is derived). The implemented
route differs from Renard's, which views `X^*(G)_k` as a sublattice of the
character lattice over `k̄`. It argues with units of the coordinate algebra
over `k` instead, and does not use a maximal torus.

## Axioms

`lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.
