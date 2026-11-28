# Compatibility of integral Harris CM witnesses on connected tests

Point transport for polarized level witnesses keeps the same rational map and
polarization multiplier. The base-change and point-transport square identifies
the orbits after transport on each leg of a common connected test. The integral
lifting isomorphism therefore also stays the same.

Actual pullback respects rationalization of each arrow. Pullback, composition
and inversion of polarized level witnesses thus give the corresponding
operations on their integral lifts. Geometric rigidity identifies the rational
isomorphisms of two witnesses between the same representatives, given
faithfulness of geometric pullback on a connected base. Injectivity of
rationalization on actual Hom groups then identifies the integral isomorphisms.

For successive pullback, `pullbackAtCompWitness` uses the canonical
composition isomorphism and multiplier one. Equality of the two presentations
of the composite point is combined with path independence on invariant orbits.
The resulting comparison is a level witness by
`HarrisPolarizedWeilLevel.levelDataBaseChange_comp_witness`. Both arrows of the
rational comparison are the rationalizations of the corresponding actual arrows.

`CompactTateCMWitness.integralIso_pullbackAt` transports a witness to the image
of the new point and pulls it back. Composing with the direct-to-successive
comparisons on the two sides gives a witness for the directly pulled-back
representatives. Rigidity identifies its actual isomorphism with the lift of
any witness on those representatives at the geometric point presented as
`𝟙 ≫ z`.
