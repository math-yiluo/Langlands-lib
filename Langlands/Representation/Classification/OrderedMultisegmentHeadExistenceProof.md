# Strong heads of ordered special-segment products

Author: Worker 950.

`Langlands.Classification.orderedMultisegmentHeadExistence` proves exactly
`Langlands.Classification.OrderedMultisegmentHeadExistence.{uF,uV} F T`
from
[MultisegmentClassificationStatement](MultisegmentClassificationStatement.md).
Its only outer parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
For every natural rank, actual segment-product datum, nonprecedence ordering
and supplied family of strong special segment heads, it supplies an actual
smooth irreducible head of that datum's normalized upper product.
The field universe `uF` and carrier bound `uV` remain independent; all segment
bases, blocks, induced products and output carriers have universe
`max uF uV`.

The implemented proof applies the published
`orderedMultisegmentHeadExistence_of_prerequisites.{uF,uV} F T` and discharges
each of its three hypotheses with a published unconditional theorem:

- `orderedSegmentSquareIntegrableConversion.{uF,uV} F T`, from
  [OrderedSegmentSquareIntegrableConversionProof](OrderedSegmentSquareIntegrableConversionProof.md),
  equips the supplied blocks with their analytic square-integrability and
  unitary normalizations, then sorts their exponents using adjacent unlinked
  swaps. It retains actual isomorphisms of the full induced products.
- `squareIntegrableEqualExponentGrouping.{uF,uV} F T`, from
  [SquareIntegrableEqualExponentGroupingProof](SquareIntegrableEqualExponentGroupingProof.md),
  groups equal-exponent runs into irreducible analytically tempered blocks,
  obtaining strictly decreasing exponents and an actual isomorphism to the
  resulting tempered standard module.
- `glRegularLanglandsHeadExistence.{uF,uV}`, from
  [RegularLanglandsHeadExistenceProof](RegularLanglandsHeadExistenceProof.md),
  supplies a strong head of this regular tempered standard module.

The imported
[OrderedMultisegmentHeadReduction](OrderedMultisegmentHeadReduction.md)
transports that head back through the two actual representation
isomorphisms using `IsIrreducibleHead.of_equiv`. This transport composes the
surjective head intertwiner with the appropriate inverse equivalence and
transports the universal kernel equality for every irreducible quotient
map. Thus the output has the full `IsIrreducibleHead` certificate, including
distinct surjective maps to isomorphic targets. The datum's original
nonprecedence and segment-head hypotheses are retained in
`SegmentProductDatum.IsLanglandsHead`.

For rank zero the same reduction uses its unconditional
`orderedMultisegmentHead_rankZero`. Positive block sizes make the block index
empty. `rankZeroNormalizedProductLinearEquiv` identifies the actual empty
tensor product and normalized induction to `GL_0(F)` with the complex line.
The resulting irreducibility and the identity quotient give a strong head
of the original product itself, with zero kernel for every irreducible
surjective quotient map.

This module is an internal composition of those published proofs. The
source statement is Rodier (1982), section 4.3, Theorem 3(a), printed
pp.211–212 (PDF pp.12–13), as documented with the registered source and
fingerprint in the target's companion Markdown. Worker 950 read that
section and the adjacent section 4.1. The local proof uses the three
proved Library inputs above; Rodier's references to Bernstein's converse
and tempered exhaustion are not substituted for proofs or added as
hypotheses. The rank-zero case has the derived provenance described above.
No parent multisegment exhaustion, square-integrable exhaustion or regular
exhaustion is used to close this theorem. The target pair and all imported
published pairs are unchanged.
