# Reduction of ordered segment-head classification

This supporting module proves the rank-zero case of
`OrderedMultisegmentHeadClassification` and reduces the unchanged all-rank
proposition to `SquareIntegrableLanglandsClassification` and
`SegmentSpecialParameterUniqueness`. The Prop-valued definition
`OrderedMultisegmentHeadClassificationReductionStatement` states precisely
that these two propositions imply the unchanged all-rank target.
`orderedMultisegmentHeadClassification_of_squareIntegrable` proves this
implication; both premises remain required when applying it. This module
does not prove either premise or the unconditional all-rank target.

The mathematical target is Rodier 1982, §4.3, Theorem 3(b), printed
pp. 211–212 (`rodier-1982-gln`). The reduction follows the square-integrable
parameter description in Henniart 2002, §§2.6 and 2.8, printed pp. 595–596.
These sources motivate the route; the proof here is an internal composition
of published Lean declarations and finite-family matching.

In rank zero, positivity of each segment degree forces the indexing set to
be empty, so every multisegment is zero and all rank-zero segment data are
equal. The existing rank-zero strong-head theorem and quotient uniqueness
then identify any two weak irreducible quotients of the same product.
That imported strong-head theorem uses
`rankZeroNormalizedProductLinearEquiv`, which identifies the induced carrier
with the complex numbers. No admissibility or strong-head condition on
the given quotients is introduced.

In positive rank, `orderedSegmentSquareIntegrableConversion` replaces each
ordered segment product by square-integrable Langlands data, preserving
the full induced representation and matching the blocks through a finite
index equivalence. The weak quotient relations transport along the
product isomorphisms.

Equality of segment multisets yields a permutation of their enumerations;
equal segments have isomorphic actual heads by comparison with the same
canonical segment head. Composing this matching with the conversion
matchings gives the block matching required by the square-integrable
classification premise, hence isomorphism of the quotients.

Conversely, the square-integrable classification premise turns an
isomorphism of the quotients into a block matching. The inverse conversion
matchings transport this back to the supplied segment heads.
`SegmentSpecialParameterUniqueness` identifies each matched pair of
segments. The resulting finite index equivalence gives multiset equality.
`RankIso` handles the equalities of block ranks and their dependent
representation transports throughout.

The private finite-list matching arguments use `List.Perm.idxBij` and
`Equiv.Perm.ofFn_comp_perm`, the same Mathlib/Batteries APIs used by the
published `TemperedBlockUniquenessReduction`. They account for repeated
segments as well as empty finite families. All declarations preserve the
independent field and representation universes of the target.
