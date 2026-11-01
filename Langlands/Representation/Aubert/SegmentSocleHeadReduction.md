# Segment exchange from an actual irreducible Aubert image

This derived intermediate result proves the explicit implication
`IrreducibleImageStatement F T → SegmentSocleHeadStatement F T`.
The irreducible-image assertion remains a hypothesis. This module supplies
neither that assertion nor the unconditional segment exchange theorem.

The more local `segmentSocleHead_of_signedIrreducibleImage` takes a segment,
its supplied strong socle `πZ` and special head `πS`, an actual irreducible
representation `τ`, and an equality `D[πZ] = δ • [τ]`, where `δ` is `1` or
`-1`. It proves the exact exchange
`D[πZ] = (-1)^(degree - length) • [πS]`. Both classes are the existing
canonical exact finite-length classes; finite length follows from the
irreducibility clauses of the strong relations. All actual short exact
sequence relations, including nonsplit ones, are retained.

The proof uses the full uniform cuspidal block shape `B`. The supplied
strong socle is a weak segment subrepresentation. The actual upper Jacquet
module of that subrepresentation is quasicuspidal by
`SegmentFullJacquet.subrepresentationJacquet_isLeviQuasicuspidal`.
Uniform reversal preserves the actual bundled Jacquet object, so the
quasicuspidal reversed-Jacquet exchange theorem applies. If
`s = (-1)^(degree - length)`, it gives
`δ • [r_B τ] = s • [reversedJacquetObject B πZ]`. Multiplication by `δ`,
whose square is one, yields the signed class equality required by
`segmentHead_of_signedJacquetClass`, with relative sign `δ * s`.

That head-identification theorem proves that the relative sign is positive
and supplies an actual equivalence `τ ≃ πS`. Since `δ * s = 1` and
`δ² = 1`, the original sign is exactly `s`. Equivalence preserves the
canonical exact classes, proving the displayed exchange. The global
conditional theorem applies the assumed irreducible-image assertion to
the supplied socle and treats its two possible signs with this local
reduction.

The substantial imported mathematical inputs have the following scope.
`QuasicuspidalJacquetExchange` proves the Jacquet identity from the actual
Jacquet compatibility of the unadjusted Aubert operator, the product-Levi
quasicuspidal eigenvalue, and actual inverse-conjugation transport; it also
identifies uniform reversed Jacquet objects.
`SegmentJacquetSubobject` derives quasicuspidality from the actual injective
Jacquet map into the increasing segment induction and hereditary
quasicuspidality of its associated Jacquet filtration.
`SegmentSignedJacquetHead` transfers a nonzero map from the reversed
Jacquet object to the decreasing tensor across a signed exact-class
identity, using a centrally separated simple series and actual central
polynomial projections. Positive composition multiplicities force its
relative sign to be positive. Normalized first adjointness and the
independently proved decreasing strong socle identify the supplied
irreducible with the supplied special head. That theorem assumes the
irreducible and the signed class identity used here.

These are lower algebraic and actual representation results. The reduction
uses no excluded analytic classification, multisegment exhaustion, or
unproved full segment Jacquet formula. The independent field and carrier
universes, arbitrary prime, supplied field and topology, saturated carriers,
strong constituent relations, upper block parabolics, and unchanged
unadjusted support-dependent sign remain those of the original target.
The provenance is an internal combination of the stated inputs and
elementary integer-sign algebra; no original-literature claim is added.

Worker 165 authored this reduction. Worker 1186 authored the actual
signed-Jacquet head-identification and central-series helpers reused in
its source closure.
