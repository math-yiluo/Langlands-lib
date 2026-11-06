# Carrier universes in supercuspidal pole existence

This is internal support for `TemperedTwistSupercuspidalPoleStatement`. It
packages the untwisted conclusion and proves that its carrier universes can
be chosen independently. It does not prove that a pole partner exists.

`HasSupercuspidalPolePartner F ψ ν π` means that some irreducible supercuspidal
smooth representation of positive rank `r + 1` has a certified pair
L-polynomial with `π` which vanishes at one. It includes `r + 1 ≤ rank π`
and the strict inequality when `π` is not supercuspidal. The source is an
actual representation in universe `uV`, and the partner is in the independently
specified universe `uW`. The Haar measure is any additive Haar measure; no
self-duality assumption is needed for transport.

`HasSupercuspidalPolePartner.of_equiv` starts with a witness and an actual
equivalence from its source to another representation. The published theorem
`Langlands.padicIrreducibleSmoothSmallRealization` realizes the irreducible
smooth partner in any prescribed carrier universe. Supercuspidality transports
through that equivalence, and `IsPadicRankLPolynomial.congr_equiv` transports
the entire polynomial certificate in both variables. The polynomial and its
root are unchanged. The weak rank bound is unchanged, and source
supercuspidality transport gives the strict bound. Applying this construction
in both directions proves `hasSupercuspidalPolePartner_iff_of_equiv`.

For `untwistedTemperedSupercuspidalPole_of_universes`, small realization first
moves the given irreducible smooth tempered representation into the source
universe of the assumed existence statement. Temperedness transports through
the actual representation equivalence. Applying that statement gives a pole
witness; the preceding transport then moves the source back and the partner
into the desired universe. Thus proving existence in a chosen pair of carrier
universes suffices for every pair.

Finally `temperedTwistSupercuspidalPole_of_universes` uses the
opposite-twist equivalence in the preceding internal module
`TemperedTwistSupercuspidalPoleTransport` between the full target and its
untwisted case.
All four carrier universes and the field universe remain independent.
The classification and analytic existence obligations are retained as the
explicit existence-statement hypotheses.

The provenance is internal: this module only combines the existing
small-realization, equivalence-invariance and opposite-twist results. It adds
no assertion from the literature and no new mathematical assumption.
