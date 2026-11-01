# Fixed measures for the two-block unipotent quotient

Module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentMeasures`.
Author: Worker 113.

This is internal measure infrastructure for the representation-free unfolding
derived from JPSS (1983), Section 4.6, printed pages 411–412. The definitions
use the published two-block subgroup and its product homeomorphism. This
module does not establish the quotient tower or a Fubini formula.

`blockHaar` is exactly the pushforward of the finite product of the two
integral-normalized upper-unipotent Haar measures by `blockUnipotentEquiv`.
It makes no new normalization choice. Haar measure transports through
`blockUnipotentHomeomorph`. The product is sigma-finite by second countability
of its factors, and its invariant measure is regular by Haar uniqueness
(`Measure.regular_of_isMulLeftInvariant`); regularity then transports through
the same homeomorphism. Right invariance follows by commuting
right multiplication with that group isomorphism and using right invariance
of each factor of the product.

`block_compatibleMeasureExists` and `fullUnipotent_compatibleMeasureExists`
apply the published theorem `QuotientIntegration.compatibleMeasureExists`
to the actual block subgroup and the full upper-unipotent subgroup. Each
subgroup is closed; the ambient and subgroup measures are the fixed regular
two-sided Haar measures. The ambient matrix group is locally compact. The
result is existence with all five fields of the published `IsCompatible`.
The full-unipotent assertion is also available from the separately published
`RankinSelberg.unipotent_compatibleMeasureExists`; this wrapper groups the
two applications of the same general existence theorem. No quotient tower
or coordinate-measure transport follows merely from these existence results.

`integerCube_mass_pos_lt_top` retains an arbitrary supplied additive Haar
measure on the rectangular matrix space over the canonical p-adic field.
The set of matrices with integral entries is an open finite product and a
compact product of copies of the integer ring. It contains zero, so Haar
positivity on nonempty open sets and finiteness on compact sets give positive
finite mass. In particular, this mass is not asserted to equal one.

All the results here are derived directly from the named Library maps,
measures and closed-subgroup existence theorem and the pinned Mathlib Haar
APIs. The JPSS passage motivates their use; no separate assertion from that
passage is being translated into a new definition.
