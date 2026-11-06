# Square-integrability criteria for special representations

Author: Worker 1765.

`Langlands.Classification.segmentSpecialSquareIntegrabilityCriterion`
proves the unchanged Library proposition
`Langlands.Classification.SegmentSpecialSquareIntegrabilityCriterion.{uF,uV}
F T`. The field universe and carrier parameter are independent; the actual
smooth representation has carrier universe `max uF uV`. There are no added
classification, factor, central-character or invariant-form hypotheses.

The theorem concerns the supplied irreducible quotient of the increasing
segment induction. It proves that the full analytic square-integrability
predicate is equivalent to existence of a unitary character of the full
center, and also equivalent to existence of an invariant positive definite
Hermitian form on that quotient's original carrier.

## Implemented proof

The published `segmentSpecialEssentialSquareIntegrability` supplies essential
square-integrability of the actual quotient. Irreducibility makes its carrier
nontrivial, and the segment degree is positive.

The first helper extracts a unitary central character from square-integrability
by applying the all-Haar predicate to an existing Haar measure on the actual
central quotient. Its scope allows any carrier universe.

For the converse, write an essentially square-integrable representation as
having square-integrable twist `ν^(-s)ρ`. Extract that twist's unitary central
character and compare it with the given central character of `ρ`, regarded
as the zero twist. The published
`exponent_eq_of_unitaryCentralCharacter` compares their scalar actions on a
nonzero vector. At the central scalar uniformizer, the determinant norm is
`|ϖ|^n < 1`, because `|ϖ| = q^(-1)`, `q > 1` and `n > 0`.
Thus the exponent equality lemma gives `s = 0`. Substitution in the original
analytic witness gives square-integrability for every Haar measure, including
all admissibility and coefficient integrability requirements.

For the second equivalence, `glSquareIntegrableUnitarity` produces the positive
Hermitian form from square-integrability. Conversely, a given invariant form
defines unitary exponent data with exponent zero.
`chosenUnitarySquareIntegrability` then gives square-integrability at that
chosen exponent. The zero-twist identity recovers the original action.

## Provenance and boundaries

This is an internal assembly of the cited published Library proofs. The
central-character normalization argument is the one described in the paired
Library statement's derivation of its fourth clause. No new theorem from the
literature is asserted or assumed here. The source correspondence and original
analytic conventions remain those documented in
`SegmentSquareIntegrabilityStatement.md` and in the imported proof modules.

The construction leaves the target statement and all its imports unchanged.
It neither supplies the centered segment parametrization nor proves the
associated-pair induction theorem. Compilation, exact-target validation,
independent semantic review and publication remain separate requirements.

The extraction of a unitary central character reuses `Langlands.RankinSelberg.nonempty_unitaryCentralCharacter_of_isSquareIntegrable` with the same supplied topology, original representation and arbitrary carrier universe.
