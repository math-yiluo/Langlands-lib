# Actual coproduct carriers and compact compression

This internal unit compares an arbitrary supplied coproduct in the smooth
category with the actual algebraic direct sum of its carriers. The group,
component-carrier and index universes `uG`, `uV` and `uI` are independent.
In particular, the index universe can exceed the carrier universe of the
coproduct vertex. The actual direct sum then has carrier universe
`max uI uV`, and the comparison is an actual representation equivalence
across universes.

`cofanDirectSumMap A s` sums the actual injection intertwiners of a supplied
cofan `s`. It is the algebraic direct-sum extension on carriers, and
equivariance follows on every summand from the equivariance of the
original injections. It sends each actual summand inclusion to the
corresponding injection of `s`.

When `hs : IsColimit s` is supplied, each component projection is constructed
by descent of the cofan that is the identity on that component and zero
on the others. Composing it with actual summation recovers the actual
direct-sum coordinate. These projections prove injectivity of
`cofanDirectSumMap`.

For surjectivity, take the actual smooth quotient of `s.pt` by the
summation image. Every injection maps to zero in this quotient. The
coproduct universal property therefore makes the quotient map itself
zero. Every vector of `s.pt` consequently lies in the summation image.
`cofanDirectSumEquiv` packages these two proofs and retains the actual
summand evaluation law.

`compressedAction_eventuallyStable_of_cofan_finite_support` assumes a
compact open subgroup `K`, a group element `g`, eventual stability of
the actual compact compressed action on each component, and finiteness
of the set of indices with nonzero actual `K`-fixed vectors. The actual
direct sum is smooth, as its injection into the smooth coproduct vertex
is equivariant and injective. The finite-support sum theorem gives a
positive stable power on that direct sum, and the actual equivalence,
read as an equivariant retract, transfers the same power to `s.pt`.

This allows a category decomposition with a large class index to use
the concrete finite-support compression theorem without identifying
the index and carrier universes. Existence of the decomposition,
compact-level finite support and stability of its components remain
explicit premises. There is no admissibility, finite length or finite
dimension hypothesis on a component or on the vertex.

Worker 1751 derives the unit from the actual smooth quotient and
direct-sum constructions, the supplied coproduct universal property,
and the published compact-compression naturality and finite-support
propagation results. No new assertion is attributed to literature,
and no representation-theoretic decomposition or uniform stabilization
theorem is proved here.
