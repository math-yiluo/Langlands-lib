# Ordered segment-head classification for GL_n

`Langlands.Classification.orderedMultisegmentHeadClassification.{uF,uV} F T`
proves the unchanged proposition
`Langlands.Classification.OrderedMultisegmentHeadClassification.{uF,uV} F T`
of `MultisegmentClassificationStatement`. The prime `p`, its `Fact p.Prime`
instance, the field `F : PadicField.{uF} p` and its topology data `T` are
arbitrary, and the universes `uF` and `uV` are independent. For every rank `n`,
including `0`, and every pair of segment-product data `d`, `d'` with weak
irreducible quotients `π`, `π'`, it gives
`d.multisegment = d'.multisegment ↔ Nonempty (π ≅ π')`. No hypothesis is added:
there is no admissibility premise, no head-kernel uniqueness assumption, and no
classification statement taken as a premise.

## Implemented proof

The proof is a composition of three proved Library theorems.

1. `orderedMultisegmentHeadClassification_of_squareIntegrable`
   (`OrderedMultisegmentHeadClassificationReduction`) proves
   `OrderedMultisegmentHeadClassificationReductionStatement`: the two
   propositions `SquareIntegrableLanglandsClassification` and
   `SegmentSpecialParameterUniqueness` together imply the all-rank target. That
   module settles rank zero unconditionally: segment degrees are positive, so
   every rank-zero datum has an empty multisegment, and any two weak irreducible
   quotients of the one-dimensional rank-zero product are isomorphic. In positive
   rank it converts each precedence-ordered segment product into
   square-integrable Langlands data with an isomorphic induced representation
   and matched blocks, through `orderedSegmentSquareIntegrableConversion`. It
   then turns block matchings into equality of segment multisets and back.
2. `squareIntegrableLanglandsClassification`
   (`SquareIntegrableLanglandsClassificationProof`) proves the first premise.
   Irreducible quotients of permitted square-integrable Langlands products are
   isomorphic exactly when their blocks match, with multiplicities, under a
   finite index equivalence.
3. `segmentSpecialParameterUniqueness`
   (`SegmentSpecialParameterUniquenessProof`) proves the second premise. Two
   special segment heads of equal degree are isomorphic only when their segments
   are equal.

The theorem applies the first theorem to the other two, all at the target's
universes `uF` and `uV`. The proof term contains no further argument. A
development check reported only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source

The mathematical statement is Rodier 1982 (`rodier-1982-gln`), §4.3, Theorem
3(b), printed pp. 211–212. Rodier derives it from Bernstein's square-integrable
classification, the tempered classification, Zelevinsky's Theorem 9.7 and the
Langlands quotient theorem. The Lean proof uses the Library's own route instead:
it goes through square-integrable Langlands data, as explained in the cited
Markdown of the three theorems above. The relation between nonprecedence
ordering and Henniart's decreasing-exponent ordering is explained in the
statement's Markdown, `MultisegmentClassificationStatement.md`, section "Order
translation".
