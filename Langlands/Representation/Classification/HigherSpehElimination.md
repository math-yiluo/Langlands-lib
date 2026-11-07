# Ordered-head reduction of higher-Speh elimination

Worker 1732. This is a derived construction and a conditional reduction for the
unitary generic exhaustion proof. Its main input is the published proposition
`OrderedMultisegmentHeadClassification.{uF,uV} F T`, retained explicitly as a
hypothesis. This module supplies no proof of that proposition or of
`UnitaryGenericExhaustion`.

The field universe `uF` and representation parameter universe `uV` are
independent. Actual smooth representations and the segments used for the Speh
construction have carrier universe `max uF uV`. The construction uses the given
p-adic field, its supplied topological data, actual normalized upper-block
induction, and actual quotient maps.

`genericLanglandsQuotient_isUnlinked` applies the proved
`genericSegmentProductExhaustion` to a generic irreducible quotient in every
positive rank. This yields an actual unlinked segment product isomorphic to the
quotient. Nonlinkage makes its labels precedence ordered. The inverse
isomorphism supplies a surjective intertwining map, so this same product is a
Langlands quotient datum. The explicit ordered-head classification hypothesis
identifies its multisegment with the original quotient's multisegment.

`nondegenerateLanglandsQuotient_isUnlinked` assumes only an entrywise Whittaker
functional on the quotient, in any positive rank. The quotient is irreducible
by its Langlands quotient predicate. Its admissibility follows from the proved
cuspidal embedding theorem. The equality of the entrywise and standard
characters then supplies the genericity hypothesis of the preceding lemma.

`segment_isLinked_twist_one` is independent of the classification hypothesis.
The proved injectivity of integral segment members distinguishes the initial
member of the original segment and the terminal member of its unit forward
twist. These two members rule out either containment of supports. Extending the
original segment by one member realizes the union of the supports. Thus a
segment and its forward unit twist are linked, including a segment of length
one.

For a segment `Δ`, a natural number `k`, and an actual representation `δ` of
rank `Δ.degree`, `centeredSegmentHeadDatum` constructs the actual
`SegmentProductDatum` with `k` rows. Row `i` is
`Δ.twist (((k : ℝ) - 1) / 2 - (i : ℕ))`, and its block is the corresponding
actual real determinant twist of `δ`. The degree is `k * Δ.degree`. Its induced
representation is definitionally the published centered uniform product, as
proved by `centeredSegmentHeadDatum_induced`; no replacement representation or
abstract product predicate is introduced.

If `δ` is a segment head, real-twist compatibility makes every row a segment
head. If `δ` is also unitarizable, a supplied positive invariant Hermitian form
gives exponent-zero unitary exponent data. Shifting these data by the centered
row exponents and applying the proved linked-head exponent comparison shows
that the rows are precedence ordered: an offending precedence relation for
`i < j` would force the decreasing real exponents to increase. For `1 < k`,
rows one and zero differ by a forward unit twist and hence are linked, proving
`centeredSegmentHeadDatum_not_isUnlinked`.

`centeredSegmentHeadQuotient_length_eq_one` combines these facts. A supplied
irreducible quotient of the exact centered induction is a Langlands quotient
of this datum. An entrywise Whittaker functional forces its multisegment to be
unlinked, assuming ordered-head classification. The two linked adjacent rows
exclude `1 < k`; the supplied positivity of `k` gives `k = 1`.

Finally, `SpehDatum.length_eq_one_of_hasFunctional` applies this construction to
the supplied Speh datum and any supplied realization of its `IsSpeh` predicate.
The base block is irreducible, unitarizable and analytically square integrable
by that predicate. The proved segment classification of essentially square
integrable representations realizes it as an actual segment head, with an
actual equality of ranks. Eliminating this rank equality reduces the given
centered quotient and entrywise functional to the preceding theorem. The
result is `d.length = 1`, for every supplied unitary additive character `ψ`.
No separate unitarizability assumption on the Speh quotient is used.

The provenance is internal and derived from the imported published
constructions and proofs: generic segment-product exhaustion, cuspidal
embedding, integral segment-member injectivity, real-twist compatibility,
linked-head exponent comparison, and essentially square-integrable segment
classification. This module makes no new assertion of an original-source
classification theorem. In particular, ordered-head classification remains an
unproved input here; the generic-free Tadic exhaustion needed for the final
unitary generic theorem is a separate obligation.
