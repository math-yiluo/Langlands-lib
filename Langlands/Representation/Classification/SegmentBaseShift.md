# Positive integral shifts between segment bases

This internal auxiliary API is derived from the published definitions of
`Segment.Precedes` and `CuspidalDatum.twist`. It is not an independent proof of
integral twist freeness or multisegment socle exhaustion.

`Segment.PositiveBaseShift Δ Γ` means that the base of `Γ` equals the base of
`Δ` twisted by a strictly positive natural number, regarded as a real number.
Linkage is not required. Every precedence relation supplies such a shift.
Successive positive shifts compose by addition, using
`CuspidalDatum.twist_twist`, and preserve the rank of the bases. Induction over
`Relation.TransGen Segment.Precedes` therefore produces a positive shift
between the endpoints of every nonempty finite precedence chain. This does not
claim that precedence itself is transitive.

All conclusions excluding cycles or reverse relations explicitly assume
`Langlands.Classification.CuspidalIntegralTwistFreeness F T` at the same
independent universes. A cycle would give
`Δ.base.twist (k : ℝ) = Δ.base` for some positive natural number `k`. Apply
the supplied freeness equivalence to the integer image of `k`; its conclusion
`k = 0` contradicts positivity. This proves
`Segment.not_transGen_precedes_self`. Composing a shift and a reverse shift
gives the same contradiction, proving the two `not_reverse` lemmas.

The only project import is the integral-freeness statement module, which
imports `Segments`. This module neither imports a proof of freeness nor adds
one by assumption to an unconditional theorem. It does not establish linkage
orientation, unlinked product commutation, linked embedding reduction, ordered
socle existence, or exhaustion. Its conditional acyclicity lemma is suitable
for use with a separately proved freeness theorem and the general inversion
exposure API. All segments retain the original field and carrier universes.
