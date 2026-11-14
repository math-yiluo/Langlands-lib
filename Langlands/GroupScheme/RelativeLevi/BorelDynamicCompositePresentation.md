# Dynamic Borel presentation over a composite base map

Worker 653, using Worker 608's actual neighbourhood presentation.

This internal transport construction takes the original Borel inclusion
`i : B → G`, commutative torus `T`, inclusion `t : T → G`, a map `b : U → S`,
and supplied `BorelDynamicNeighbourhoodData` for their pullbacks to `U`.
If `q` is the supplied neighbourhood projection, it produces
`BorelDynamicPresentationData i T t (q ≫ b)` in the actual direct pullback
over the composite map.

The payload contains splitness of the direct pullback torus, a cocharacter of
that torus, equality of the pulled back positive Borel range with its dynamic
parabolic, equality of its full dynamic centralizer with the pulled back torus
range, and actual closed relative Borel data for its opposite cocharacter.
The equalities are subgroup functor equalities on every test scheme.

`borelDynamicCompositePresentation` uses the canonical isomorphisms
`Descent.pullbackComparison b q (q ≫ b) rfl` for the original ambient group,
Borel and torus. It composes the supplied cocharacter with the commutative
torus comparison. Naturality identifies its composite with the torus inclusion
with the supplied ambient cocharacter followed by the ambient comparison.
Splitness transfers through the torus isomorphism. Range transport and the
isomorphism invariance of dynamic parabolics and centralizers transfer the two
equalities by inverse image along the inverse ambient comparison.

The negative Borel's source group is the supplied source group itself. Its
inclusion is composed with the ambient comparison. Its relative Borel and
closedness certificates transfer through that isomorphism; dynamic parabolic
transport, together with associativity for the opposite cocharacter, proves
the resulting range equality.

This is an internal composition of the stated pullback, range and dynamic
transport interfaces. It makes no additional mathematical existence claim
and chooses no cover or point neighbourhood. All geometry, splitness and
dynamic certificates are supplied by the neighbourhood data. In particular,
this construction alone does not prove the global opposite Borel statement.
