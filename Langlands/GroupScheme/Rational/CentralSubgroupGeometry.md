# Commutativity and positive dimension of central subgroups

This derived development retains the actual subgroup and action constructed
in `Rational.UnipotentSmoothCenter` and supplies two further properties.
All declarations retain an arbitrary universe `u`.

A central group-scheme homomorphism whose underlying map in the over category
is monic has a commutative source. On every scheme test, cancellation reduces
commutativity to the centrality of the two image points. The criterion for a
commutative monoid object then gives `IsCentral.isCommMonObj`.
`IsCentral.commGroupScheme` packages the unchanged source group scheme as an
actual `CommGroupScheme`; its underlying object, group law and all morphisms
are unchanged. This constructor works over any base scheme.

Over a separably closed field, a smooth connected separated group with a
nontrivial image under a supplied group-scheme homomorphism has positive
relative dimension. The published `smoothConnectedRelativeDimension` theorem
first supplies a natural dimension. If it were zero, the structure morphism
would be étale. The published
`isIso_of_connected_separated_etale` theorem would make it an isomorphism.
Cancellation against that structure morphism then makes every scheme-valued
point of the group equal to the unit. This forces the supplied image functor
to be bottom, contrary to the hypothesis. No properness hypothesis is used.

The final theorem combines these two arguments with the constructed smooth
stable central subgroup of a nontrivial smooth connected affine unipotent
group. Over a separably closed field and for any affine acting group it gives
an actual commutative, smooth, affine, geometrically connected and connected
central closed subgroup of positive relative dimension, stable under the
given action. The restricted actual action, nontrivial range and inclusion
equivariance on every test scheme are retained.

The provenance is the explicit cancellation and dimension-zero arguments
above using the named Library theorems and the previously constructed smooth
centre. This development does not assert unipotence of the subgroup, vector
coordinates, p-torsion or equivariant linearity. The exact
`CentralStableVectorSubgroupStatement` and host ordered-product theorem remain
open.
