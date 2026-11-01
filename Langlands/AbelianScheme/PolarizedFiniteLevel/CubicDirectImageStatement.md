# The canonical direct image of the cubic diagonal bundle

For an existing ordinary polarized datum `a : Datum P S g d n`, put
`L = a.canonicalBundle` and `E = a.rigidificationModule = pi_*(L^3)`.
The polarization has the original degree `d^2`, and the datum retains its
original dual witness. This module defines the actual comparison
`b^* E -> E'` for every morphism `b : S' -> S` and states its expected
invertibility together with the prescribed finite local rank.

The construction `Datum.rigidificationBaseChangeMap` uses the published
`DerivedSections.pushforwardBaseChange` for the Cartesian square of
`pi` and `b`. That is the canonical sheaf base-change morphism, defined
using the actual pullback/pushforward adjunction units and the
pushforward comparison around the square. Its target is initially
`pi'_*(q^*(L^3))`, where `q` is the total-space projection.
The inverse of `Datum.cubicBundlePullbackIso` identifies the coefficient
with the actual cubic bundle of `a.pullback b`; pushing forward this
inverse gives the stated target `E'`. No choice of an isomorphism of
abstract section modules replaces this specified map.

`CubicDirectImageStatement` says that for every locally noetherian base,
every published `Prerequisites`, every dimension `g`, positive
polarization index `d`, and arbitrary level `n`, the module `E` is
locally free of rank `6^g*d`, and this specified comparison is invertible
for every base morphism. The changed base is an arbitrary scheme in the
same universe. In particular, there is no flatness hypothesis on the
base change. `IsLocallyFreeOfRank` is the published finite local-basis
predicate, with each basis indexed by a type equivalent to
`Fin (6^g*d)`. The assertion does not assume a frame for `E`.

The source is Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
third edition (1994), Chapter 7, Definition 7.5 and its base-extension
discussion, printed page 130 / one-based PDF page 143. It is registered
as `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
There the rank is `6^g*d` (the mark following `d` refers to the footnote).
The text derives the assertion from Propositions 6.10 and 6.13.
The Lean formulation is its internal specialization to the actual
published datum and canonical sheaf comparison. The level structure
does not enter this geometric assertion, so no positivity or coprimality
condition on `n` is imposed.

This module states the direct-image theorem and does not prove it.
It constructs no projective bundle, relative embedding, moduli scheme
or representation of the ordinary functor.
