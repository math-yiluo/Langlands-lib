# Rational lifting of actual E7 inversion

This internal helper first shows that full-torus inversion restricts along every
commutative group-scheme homomorphism. Applied to the actual map from the
base-changed distinguished split torus into the absolute pinning torus, this
identifies the induced action on the split torus with inversion. The published
relative Weyl restriction proof lifts that actual action to a rational normalizer
point, retaining its geometric inverter as a comparison witness.

The hypotheses identify every ordered integral E7 Cartan entry and simply
connectedness of the ambient group. They do not assert a centre movement result.

The entry proposition `Langlands.GroupScheme.TitsIndexData.E7RationalInversionStatement` records the precise scope of
`exists_rational_normalizer_and_geometric_inversion_of_E7`: its explicit hypotheses are universally quantified in a
Prop-valued definition. The implemented theorem and proof are retained.
This unit is submitted as a statement because its mathematical entry is
a proposition, rather than a data construction.
