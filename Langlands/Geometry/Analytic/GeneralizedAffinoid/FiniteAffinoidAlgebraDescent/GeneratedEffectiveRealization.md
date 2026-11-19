# Effective realization from local module generation by matching sections

Let `K` be a complete ultrametric normed field, including trivial valuations.
Take the original finite full-domain cover of the spectrum of a presented
positive-polyradius affinoid algebra, the supplied finite Banach local
algebras, and the ordinary descent datum. Suppose a single finite tuple of
matching sections projects to module generators over each original cover
algebra. This construction produces the entire `EffectiveRealization`.

The previously constructed generator quotient gives a bounded matching
presentation. Its structural map is the original weighted coefficient map
followed by the quotient map, as checked after the injective matching
evaluation. The original local quotient equivalences identify the local
maps of that presentation. This uses the entire inverse identities of
`matchingEquiv` and the restrictions of its glued inverse. The corresponding
cover member in the quotient has precisely the inverse image of the original
domain's locus.

The actual pushout along the original stored cover map and the given local
algebra both represent this same full domain in the global presented
algebra. Bounded domain uniqueness gives their comparison equivalence.
The forward map agrees with the entire canonical comparison because both
maps agree on the representing map from the global algebra.

The square-zero coefficient lift theorem gives the finite Banach structure
on the original matching-valued structural map. The established realization
assembly transports this bound to the presented structural map and provides
all exact overlap and spectrum fields for the original cover.

This internal construction combines the effective closed-kernel quotient,
the uniform coefficient bounds, and the full-domain universal property.
