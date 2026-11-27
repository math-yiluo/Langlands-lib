# Lower packet densities on the actual full convergence domains

`Langlands.HarishChandraSchwartz.WeakExpansion.lowerPacketDensityAtCompact`
proves `LowerPacketDensityAtCompactStatement` for all of its parameters. The
field and the representation carrier have independent universes. The theorem
gives a `LowerDensityPackage` for the conjugated inducing representation on the
dynamic Levi of the lower cocharacter. Its compact is the literal preimage
`leviSchemeCompact` of the given compact under the standard Levi inclusion. The
package contains `ForwardContinuation` and `ReverseContinuation` data on the
entire forward and reverse convergence domains, at the lower compact and with
the original quotient Haar measures of the two opposite integrals. No openness
of these domains is used.

## Central quotients

Three general lemmas concern a locally compact Hausdorff second-countable group
`G`, a normal subgroup `C` contained in the center, and a Haar measure on
`G / C`.

- `centralQuotientProjection_map_isHaarMeasure_of_isSquareIntegrable`: let the
  compact open subgroups be cofinal among open subgroups, and let an irreducible
  representation be square integrable modulo `C`. Then the pushforward of the
  Haar measure along `centralQuotientProjection` to `G / Z(G)` is a Haar measure.
  Compact-open duality gives a nonzero smooth functional and a coefficient that
  is nonzero at the identity. The published
  `centralQuotientProjection_map_isHaarMeasure` applies to this coefficient.
- `isSquareIntegrableModCenter_map_centralQuotientProjection`: the same
  representation is square integrable modulo the full center for this
  pushforward. The proof uses `centralSubgroupCoefficientNorm_memLp_map`. The
  coefficient norm modulo the full center agrees pointwise with the norm on
  `G / Z(G)`.
- `centerQuotientHaar_isInvInvariant`: if the modular character of `G` is
  trivial, every regular Haar measure on `G / Z(G)` is invariant under inversion.
  It is right invariant by `Haar.centralQuotient_isMulRightInvariant`, and
  `isInvInvariant_of_isMulRightInvariant` gives inversion invariance.

## Continuations for an arbitrary quotient Haar measure

`actualOppositeFullDomainContinuation_of_isHaarMeasure` has the conclusion of
the published `ActualOppositeFullDomainContinuationStatement`. That conclusion
gives continuation data for the forward and reverse compact families on their
entire convergence domains and a nonempty open subset of each domain. The new
theorem assumes square integrability modulo a central subgroup `C` for an
arbitrary Haar measure on `levi χ / C`. Inversion invariance of that measure is
not assumed. The Levi is closed, hence locally compact, and it is second
countable as a subspace. The full center is closed. The quotient by the center
is therefore Hausdorff, locally compact and second countable, and its Haar
measures are regular. The proof pushes the measure to `levi χ / Z(levi χ)` with
the first two lemmas. The modular character of the Levi is trivial by
`DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one`, so the
third lemma makes the pushforward invariant under inversion. The published
theorem `actualOppositeFullDomainContinuation` then applies to the full center.
The continuation types use the published proofs `relativeRootReflectionExistence`
and `centralSplitTorusCharacter` of the two structural propositions. They agree
definitionally with the types for any other proofs of these propositions.

## The lower density

In the proof of `lowerPacketDensityAtCompact`, the central subgroup, its quotient
Haar measure and the representation are transported to the lower dynamic Levi by
`lowerCentral`, `lowerMeasure` and `lowerRepresentation`. Square integrability
transfers by `lowerRepresentation_isSquareIntegrable`. The standard Levi Iwasawa
hypothesis gives the factorizations of the lower ambient group through the
parabolic of the lower cocharacter and through its opposite, with the lower
compact. The previous theorem applies to the lower ambient group
`lowerAmbient_isConnectedReductive`, the lower cocharacter and the irreducible
conjugated representation. Its forward and reverse continuations and nonempty
open subsets of the domains go into `lowerDensityFromOppositeContinuations`. The
compact of the resulting package is the literal lower compact by definition.

## Source

The lower densities enter the rank induction of Waldspurger (2003),
Proposition VI.3.1, printed p. 304, in the registered source
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Theorem
IV.1.1 and its proof, printed pp. 277–281, give convergence on a translated cone
and rationality of the standard intertwining integrals. The Library's
continuation data ask for more. Its one denominator must be nonzero on the entire
convergence domain and clear the original integral there. The full-domain
continuation theorem supplies these conditions. The central-quotient lemmas are
internal measure-theoretic steps without a separate source.
