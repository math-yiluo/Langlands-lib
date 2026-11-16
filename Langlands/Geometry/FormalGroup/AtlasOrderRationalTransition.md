# Actual full-order transition isomorphisms and rational transition squares

This internal module equips every actual transition of a
full-order formal atlas with its full-order formal isomorphism.
The original transition's forward map commutes with the order by
the atlas's data; `OrderIso.ofModuleIso` derives commutation for
the original inverse. Thus `transitionIso` retains exactly the
original two formal maps and both inverse equations.

The same-chart identity and cocycle laws hold as identities of
these full-order formal isomorphisms. Their proofs use
forward-map extensionality and the underlying atlas's formal
identity and cocycle equations.

The scalar and coefficient rings are arbitrary commutative rings,
the acting order is any algebra ring, and coordinate types are
finite. Covers may be infinite. For a rational atlas map, its two
original covers agree; `sourceChart` uses this exact equality to
match the source indices. Test algebras have the coefficient-ring
universe. Rational maps use the specified scalar algebra field;
quasi-isogenies additionally require the scalar ring to be a domain
and that field to be its fraction field.

`RationalHom.onChart_transition` lifts the existing actual tensor
transition equation into the full-order tensor centralizer.
`QuasiIsogeny.onChart_transition` proves equality of the two entire
actual full-order quasi-isogeny routes around the same square.
Its proof uses forward-map extensionality and that rational
transition equation, so the uniquely determined inverse maps also
agree.

The provenance is internal from `BasicAtlas`'s actual transitions,
`OrderAction`'s actual commutation equations, and the proved tensor
transition equation in `AtlasRationalMorphism`. No implication from
equality of evaluated points to equality of formal or rational
maps is used. Normalized framing coherence, collapse of comparison
chains, coefficient descent, height laws and representability are
separate obligations.
