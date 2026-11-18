# Actual pinnings and highest weights under an ambient group isomorphism

This internal transport construction retains a supplied pinning's actual
torus, integral lattices, root datum and base while composing its torus
inclusion with an actual ambient group-scheme isomorphism.

The root-datum predicate transports by `IsRootDatumOf.comp_iso` in
`RootDatumTorusTransport`. The simple-root Lie trivializations compose with
the actual weight-space differential equivalence. Consequently the new root vector
is the original root vector mapped by the actual group differential.

The character spaces of a representation on the target group coincide
with those of its pullback along the group isomorphism. Pulling an
original representation to the target along the inverse isomorphism
therefore preserves every original character space. This gives the
highest-weight transport theorem, using all-test irreducibility
transport, the complete torus-weight decomposition and the unchanged
positive-root monoid.

This is used for transporting the
standard special-linear highest-weight calculation through an actual
norm-one splitting isomorphism. It introduces no new existence,
cohomological or descent-effectivity premise.

The construction works over every field `k : Type u`, with no restriction
on characteristic, perfection or smoothness of the centre. Its
provenance is internal, as an explicit specialization of published
all-test root, normalizer and differential transport to the identity map
of the torus, followed by representation restriction and composition.
