# Actual quotient charts for a supplied root base

This derived construction keeps the actual affine split reductive model and
its coordinate maximal torus while allowing an arbitrary supplied root base.
In particular, the base may be the one constructed from a supplied relative
Borel by `AffineRegularBorel.adaptedBorelRootBase`. No assertion is made that
an initially chosen pinning is adapted to that Borel.

`AffinePinnedModel.withRootBase` keeps the original group, inclusion, full
coordinate root datum, fibrewise realization and free root lines. It replaces
the chosen base by the supplied one. The chosen trivialization of each new
simple-root line supplies its pinning; no conjugation of the actual group
or torus occurs.

For any actual full fppf quotient of the coordinate torus by the inverse
image of the full ambient centre, `adjointQuotientChart` is the unique
comparison with evaluation on the supplied simple roots. The theorem
`adjointQuotientChart_fac` identifies its composite with the quotient map
as the actual character projection, on all relative test schemes.

`adjointQuotientChartOver` pulls this chart to any scheme over the original
affine base. Its factorization uses the canonical split-torus base-change
isomorphisms on source and target. Thus it is the actual normalized
simple-root character projection on that base, with the same exponents and
support. There is no flatness, reducedness or connectedness assumption on
this change of base.

The auxiliary `RelativeRoot.IsFppfQuotient.iso_comp` transports a full fppf
quotient through a supplied source isomorphism. It preserves flatness,
surjectivity and local finite presentation and identifies the full actual
kernel by inverse image. `adjointQuotientOver_isFppfQuotient` applies it to
the canonical split coordinates after arbitrary base change.

The proof reuses the affine pinned model's full root-kernel identification,
the fppf property of the independent simple-root projection, and uniqueness
of full fppf quotients. The base-change factorization is functoriality
followed by the actual character-projection base-change theorem. The full
centre, including finite or non-smooth factors, remains the kernel. Empty
simple-root supports are allowed. This module does not construct an etale
cover adapted to a supplied torus, compare its overlap fibres or perform
effective descent.
