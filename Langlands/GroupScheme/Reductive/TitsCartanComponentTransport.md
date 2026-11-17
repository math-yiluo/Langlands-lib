# Cartan component transport and the full stabilizer action

Worker 509. These are internal consequences of the actual Tits-index and
Cartan-component definitions, with no added structural or arithmetic premise.
They apply over arbitrary fields at every universe parameter.

Connectivity transports along an injective vertex map preserving every ordered
integral Cartan entry. The proof uses the four constructors of the equivalence
closure: an edge, reflexivity, symmetry, and transitivity. A star element gives
such a map, because its root-datum automorphism preserves the pairing; its
inverse proves reflection of connectivity.

`cartanComponentStabilizer` is the subgroup of the full absolute Galois group
whose elements take the chosen vertex into its connected Cartan component.
Connectivity preservation proves closure under multiplication and inverses.
`cartanComponentStarPerm` restricts each such element to a permutation of the
entire actual component. `cartanComponentStarRepresentation` packages those
permutations into a monoid homomorphism. The same Galois element acts on every
vertex, and all ordered Cartan entries are preserved.

`TitsIndexEquiv.cartanComponentEquiv` restricts an actual index equivalence to
its connected components. Applying the forward and inverse vertex equivalences
proves the connectivity comparison. The restricted equivalence intertwines
each star element, and the two component stabilizers are equal as subgroups of
the same absolute Galois group.

For equivalent indices of the same actual group,
`TitsIndexEquiv.componentFactor` transports a complete `ComponentFactor`
witness. It retains the finite separable extension, the actual absolutely
almost-simple simply connected group and its Tits index, the complement, the
central-isogeny cover, and the anisotropy implication. Its vertex equivalence
is the original equivalence composed with `cartanComponentEquiv`. Ordered
Cartan preservation follows by transitivity of the two pairing equalities.
Connectivity reflection supplies the original stabilizer hypothesis. For each
of the two lift clauses, the original witness supplies one Galois element
working for every vertex, and the index equivalence's `star_eq` transports
that same element and the entire pointwise equality.

The provenance is derived interface material for constructing the prescribed
`TitsIndexData.ComponentFactor`. No component-factor existence, root-factor
compatibility, local classification, or Kneser–Tits result is used or proved here.
