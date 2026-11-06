# Centered unitary segment parameters on the supplied action

This internal construction describes each supplied irreducible
square-integrable representation of positive rank by a segment with an
actual unitary supercuspidal base. Field and carrier universes `uF` and `uV`
are independent. Every representation uses the supplied compatible topology
and retains its carrier in `Type (max uF uV)`.

`exists_unitaryMidpointBase_of_isSquareIntegrable_segmentHead` starts with
an actual strong segment head `π` for a segment `Δ`. It proves that the base
of `Δ.twist ((Δ.length - 1) / 2)` has an actual supercuspidal representative
with an invariant positive definite Hermitian form. Here and throughout,
the midpoint uses real casts and real division.

The proof takes the original supercuspidal representative from the head
relation and applies `supercuspidalRepRealUnitarization`, obtaining an actual
unitarizable twist by a real exponent `t`. Real-twist compatibility makes
the twist `ν^t π` a strong head of `Δ.twist t`. The centered-special theorem
then makes `ν^(-m)ν^t π` square-integrable, where
`m = (Δ.length - 1) / 2`. The original `π` is square-integrable as well.
The published `exponent_eq_of_isSquareIntegrable`, applied on a nonzero
vector supplied by irreducibility, forces `m - t = 0`. Thus this actual
unitarizable base representative represents exactly the midpoint-twisted
base. No replacement of the head action is involved.

`exists_segmentHead_unitaryMidpointBase_of_isSquareIntegrable` applies the
published unconditional segment classification to the supplied
square-integrable representation. It returns a segment, its exact degree
equality with the original rank, its strong head relation after that rank
transport, and the actual unitary midpoint-base representative above.
The square-integrability premise is transported along the same rank
equality before applying the first lemma.

`exists_centeredUnitarySegmentHead_of_isSquareIntegrable` twists that segment
by its midpoint. It returns a segment with an actual unitary base and a
strong head relation on the positive midpoint twist of the supplied action.
Twisting preserves length, rank and degree. Consequently the original
action is recovered by the negative midpoint twist, using
`realPowerTwist_neg_cancel`; the result does not choose a new carrier or
pass merely to an isomorphism class.

`SquareIntegrableSegmentParameter F T n π` stores this original segment,
the explicit equality of its degree with `n`, the actual unitarizable
supercuspidal representative of its midpoint-twisted base, and the original
strong head relation on `π` transported by that degree equality. The constructor
`squareIntegrableSegmentParameter` chooses these data using
`exists_segmentHead_unitaryMidpointBase_of_isSquareIntegrable`. It retains the
supplied action and does not choose a replacement carrier. The stored original
segment is available for subsequent parameter-uniqueness comparisons.

The provenance is an internal derivation from the published segment
classification, real unitarization, twist compatibility and exponent
comparison, together with the centered-special proof supplied with this
candidate. No additional classification, central-character, factor-formula
or gamma-comparison premise is introduced. This construction supplies a
normalization adapter for the associated-pair induction proof. It does not
prove segment-length matching, unitary-generic exhaustion, any local-factor
identity, or the induction theorem itself.
