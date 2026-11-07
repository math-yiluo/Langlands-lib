# Reduction of tempered supercuspidal pair poles

This internal adapter combines the selected-block certificate, the rank
argument, carrier-universe transport and opposite-real-twist transport.
`TemperedTwistSupercuspidalPoleReductionStatement.{uF,uV,uW}` states that
tempered block exhaustion for the canonical topology, the square-integrable
pair formula and the tempered product formula imply the unchanged
`TemperedTwistSupercuspidalPoleStatement.{uF,uV,uW}`.
`temperedTwistSupercuspidalPoleReduction` proves this implication.

The premises are precisely:

- `Classification.TemperedBlockExhaustion.{uF,uV}` for every prime and every
  `PadicField.{uF}`, with its canonical topological data;
- `SquareIntegrableLFactorStatement` with field universe `uF` and all four
  carrier universes `max uF uV`;
- `TemperedLFactorStatement` with field universe `uF` and both carrier
  universes `max uF uV`.

The equal-rank supercuspidal formula is supplied by the published
`supercuspidalEqualRankLFactor` theorem. It is not a remaining premise.
The three listed premises are not proved here. Thus this contribution is
conditional support for the pole-existence task and does not complete its
unconditional target.

`hasSupercuspidalPolePartner_of_selectedBlockPole` first unpacks
`TemperedSupercuspidalPoleBridge.HasSelectedBlockPole`. It retains the actual
equivalence from the source to a normalized induction, the selected block
index, the exact centered-segment rank sum, the smooth irreducible
supercuspidal seed, and its component certificate. The bridge also supplies
an actual smooth irreducible supercuspidal partner, a full
`IsPadicRankLPolynomial` certificate for the source and partner, and a root
of that polynomial at one.

The proof applies `selectedCenteredSegment_rankBounds` to those same data,
reversing the outer induction equivalence to match its interface. Smoothness
comes from the actual bundled block representations. This gives seed rank
at most source rank, and strict inequality if the source is not
supercuspidal. The equality-case argument is contained in the imported rank
theorem: positive block ranks force one ambient block and a length-one
centered segment, whose actual equivalences identify the source with the
supercuspidal seed.

The partner initially has carrier universe `max uF uV`. The proof packages
all the witnesses as `HasSupercuspidalPolePartner` and applies its
`of_equiv` theorem to the identity equivalence of the source. The published
small-realization result behind that transport gives a partner in arbitrary
`uW`, preserving the rank, irreducibility, supercuspidality, complete
polynomial certificate and root.

`untwistedTemperedSupercuspidalPole_of_remaining_inputs` excludes rank zero
using the positive-rank premise and writes the source rank as a successor.
It applies `hasSelectedBlockPole_of` with the supplied exhaustion and two
product formulas and with the proved equal-rank supercuspidal formula.
The preceding adapter produces the exact untwisted target in the prescribed
carrier universes.

Finally, `temperedTwistSupercuspidalPoleReduction` applies
`temperedTwistSupercuspidalPole_of_untwisted`. That published theorem twists
the partner by the negative of the source's real exponent. Opposite real
determinant twists preserve the entire pair L-polynomial, and the partner's
irreducibility and supercuspidality are preserved. The rank conditions refer
to the original source and remain those already obtained above.

The provenance is internal: the module only composes the named mathematical
interfaces, without a new claim about the literature. The selected-block
interface and its partner construction are Worker 1779's contribution;
its classification helper was developed by Workers 1722 and 1779.
Those modules are imported at their own paths, without copying their
arguments into this adapter.
