# Finite local components of idele cohomology in towers

This internal supporting module relates the actual idele cohomology tower maps
to the finite-place localization maps. For compatible places in a tower of
number fields, localization commutes with inflation and with restriction in
every natural-number degree. The coefficient of an included idele is the
completed embedding of its lower coordinate. The automorphisms in both squares
are the existing decomposition homomorphisms and their actual restrictions.

The inflation square and its invariant, vector, and sum consequences use a
scalar tower `F ⊆ E ⊆ L` of number fields with both `E/F` and `L/F` Galois.
The restriction square uses a scalar tower `F ⊆ K ⊆ L` with `L/F` Galois;
`L/K` is then Galois, and `K/F` need not be Galois. In each square the chosen
upper place lies over the intermediate and base places, and the intermediate
place lies over the base place. The coordinate inclusion formula alone only
requires number fields `E ⊆ L` and an upper place over the lower place, with
no Galois assumption.

`finiteIdeleInvariantVector` packages the finite invariants of a class as an
additive homomorphism to finitely supported functions on the finite places of
the base field for a Galois extension `E/F` of number fields, with one chosen
place of `E` above each finite place of `F`. Its finite support comes from the
published local support theorem and the local image laws.

Consequently, for a supplied local invariant family satisfying inflation
compatibility, inflation preserves each finite idele invariant at compatible
places. If the same family also has the local image laws, both its finitely supported vector and its finite sum of
invariants are preserved when the chosen upper places lie over the chosen lower
places. These choices and both properties of the supplied family remain explicit.
All global fields have an arbitrary common universe.

The proofs are internal derivations from `IdeleCohomologyTower`,
`IdeleFiniteInvariant`, and `CompletionTower`. The construction of the idele
inclusion gives the coordinate formula after identifying a chosen lower place
with the contraction of the upper one. The decomposition homomorphisms commute
with normal restriction and with scalar restriction. Mathlib's composition and
congruence laws for cohomology maps then give the two localization squares.
The inflation law of the supplied local invariant family gives equality of each
finite summand, and equality of functions gives equality of their finite sums.
`ReciprocityTower` supplies the imported completion infrastructure; its analogous
results for field-unit cohomology are not substituted for idele cohomology.

This module does not address archimedean invariants, multiplication of total
invariants under restriction, or construction of the global invariant family.
It does not prove `GlobalInvariantStatement`.
