# Actual simple-character data from based coordinates

For a supplied `BasedCoordinateIso d` over an arbitrary scheme, the
construction `d.simpleEquiv` is a bijection from the source simple support
to the target simple support. It is the inverse root-index equivalence
restricted to those supports, using the recorded based-support law.
The theorem `indexEquiv_simpleEquiv` states its exact root-index identity.

`d.commTorusIso` is the same prescribed torus isomorphism in the
commutative-group category. `commTorusIso_square` retains its exact inclusion
square with the original group isomorphism.
`simpleCharacter_congr` states equality of actual source simple characters
transported by this isomorphism with the target simple characters indexed by
`d.simpleEquiv`. These are morphism equalities over the whole base, not only
equalities of values on one affine test.

This is an internal extraction from the existing `BasedCoordinateIso`
structure and fixed-exponent character formula:

1. `exponentCharacter_pullback` proves equality of the actual pullback of
   every fixed-exponent target character with the source character having
   exponent `d.rootEquiv.weightMap m`. Character extensionality reduces this
   equality to all relative points, where the exponent-character evaluation
   formula and `d.characters` give the result.
2. `simpleEquiv` restricts the recorded root-index equivalence using
   `d.simple_iff` and reverses it. Its index identity and the root-pairing
   equivalence's root-preservation law give `simpleRoot_weightMap`.
3. To prove `simpleCharacter_congr`, compose with the actual torus
   isomorphism, apply step 1 to the target simple root, and use step 2 to
   identify its source exponent.

Only the coordinate index types must be finite. The root-index types have
no additional finiteness hypotheses in this extraction. The module assumes
the complete based data; it supplies no existence theorem for that data,
pinning corrections or canonical comparisons.
