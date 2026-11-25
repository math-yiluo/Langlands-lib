# Transport of unique Levi witnesses containing a prescribed group

This derived helper transports the actual data in a `TorusLeviWitness`.
Ambient preservation of the relative Levi predicate is supplied by
`IsRelativeLeviSubgroup.comp_iso` from `RelativeLevi.AmbientTransport`.
There is no additional transport hypothesis.

`ofRangeEq` changes the prescribed commutative group and homomorphism when
its subgroup functor is unchanged, retaining the chosen Levi group and its
inclusion. Containment and uniqueness are transported through the given
equality on all test schemes.

`compIso` postcomposes the Levi inclusion with an ambient isomorphism.
Containment is preserved under postcomposition. A competing Levi is
composed with the inverse isomorphism, compared using the original
witness's uniqueness, and then transported back.

`transport` combines these constructions for a commuting square whose
horizontal ambient and prescribed-group maps are isomorphisms. It keeps
the original Levi group and uses the composite of its inclusion with the
ambient isomorphism. The projection lemmas record those choices.

The provenance is composition of range transport, relative Levi transport
and the original witness's uniqueness; no new geometric existence result
is asserted.
