# Actual Euler factors of centered segment bases

This internal adapter retains the actual midpoint-base representatives chosen by
`SquareIntegrableSegmentParameter`. It assumes the equal-rank supercuspidal
L-factor formula at the field and saturated carrier universes. It does not prove
that formula or the associated-pair induction statement.

`positiveBase` transports the chosen smooth representation along the equality
between its positive rank and `(rank - 1) + 1`, as required by the pair-factor
interface. Equality elimination preserves irreducibility, supercuspidality and
unitarizability. Neither the carrier nor the action is replaced by a newly chosen
representative.

If two original segments are equal, their midpoint-twisted base classes are
equal. The two actual chosen representatives therefore have equal supercuspidal
isomorphism classes. The proof uses the quotient's isomorphism criterion, forgets
the full-subcategory isomorphism to smooth representations, and transports the
resulting action equivalence along the same rank equalities.

`centeredSegmentBaseEulerFamily` applies the existing actual smooth-dual family
construction to these transported bases. For every ordered pair it retains finite
unit-circle Euler data at the actual residue cardinality and the symmetric
pair-polynomial certificate for the first base and the actual smooth dual of the
second. Given whole-segment matching, the final theorem applies the proved
original-action matching criterion and smooth bidual construction to establish
all `BasePairConditions` for the actual reciprocals.

For an actual unitary generic block datum, the last theorem uses the published
involutive Hermitian matching and full segment-parameter uniqueness to supply
one permutation satisfying numerical `SymmetricBlockData`, equality of the
matched original segments, and all these analytic base-pair conditions. The
nonnegative numerical length parameter is the original segment length minus one.

The provenance is composition of the published centered segment parameters,
supercuspidal isomorphism-class criterion, rank transport, and actual smooth-dual
Euler construction. No new external mathematical assertion is used. The field,
representation parameter, and family index universes are independent; each
chosen carrier is in the existing saturated universe `max uF uV`.
