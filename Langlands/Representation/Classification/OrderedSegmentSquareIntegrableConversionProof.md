# Ordered segment products as square-integrable Langlands data

Author: Worker 17.

`Langlands.Classification.orderedSegmentSquareIntegrableConversion` proves the
published proposition
`Langlands.Classification.OrderedSegmentSquareIntegrableConversion.{uF,uV} F T`.
Its outer parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The theorem has no additional hypotheses outside the named proposition.

For every positive rank and precedence-ordered segment-product datum whose
supplied blocks are strong segment heads, it constructs one
`SquareIntegrableLanglandsDatum` with an actual isomorphism of the full
normalized induced products. A bijection locates every original block in this
same output datum, with its dependent rank equality and actual block
isomorphism. Each occurrence is retained, including repeated or equal
segments. The field and carrier universes are independent, and segment bases,
blocks and induced carriers remain in `Type (max uF uV)`. All constructions
use the supplied `T.topology`.

## Analytic data on the original blocks

The local fact `hblock` gives both essential square-integrability and a
nonempty `UnitaryExponentData` for each actual block. The published
`segmentSpecialEssentialSquareIntegrability.{uF,uV} F T` applies to the
weak segment-quotient relation obtained from its strong head witness.
Unpacking the resulting analytic predicate supplies a real number `s` for
which the negative-exponent real norm twist of that original block is
square-integrable.

Headhood makes the block irreducible, and `isIrreducible_twist_iff` preserves
irreducibility on this twist. Each segment degree is positive. The published
`glSquareIntegrableUnitarity.{uF,max uF uV}` therefore supplies an actual
invariant positive definite Hermitian form on this same twisted carrier.
Together `s` and that form give `UnitaryExponentData`. Thus the output's
analytic field is the genuine `T.IsEssentiallySquareIntegrable` predicate,
and its normalization contains the required positive form.

## Sorting with actual product isomorphisms

Choose a fixed unitary exponent datum `u i` for each original position. For a
permutation `σ` sending new positions to original labels, the invariant `P σ`
consists of precedence ordering of `d.permute σ` and an actual isomorphism
from `d.induced` to `(d.permute σ).induced`. The identity permutation satisfies
this invariant by the supplied ordering and the identity isomorphism.

Consider a strict adjacent increase of the chosen real exponents. If those
two segments were linked, the first clause of the published
`linkedSegmentHeadExponentComparison.{uF,uV} F T`, applied to their actual
original blocks and fixed exponent witnesses, would contradict the current
nonprecedence ordering. Hence this adjacent pair is unlinked.
`IsPrecedenceOrdered.permute_adjacentSwap` preserves the ordering. The
published `adjacentUnlinkedSegmentSwap.{uF,uV} F T` supplies the actual
isomorphism of the entire current induced product with the product after
this swap. Composing it with the invariant's current isomorphism proves
`P ((Equiv.swap j (j+1)).trans σ)`, with the exact finite-index bounds in
Lean. The induction-functor endpoint in the adjacent theorem is
definitionally the induction of the permuted datum.

`Combinatorics.finitePermutationSorting` now yields a permutation preserving
`P` and making the chosen exponent family antitone. Its published proof
minimizes the position-weighted sum among invariant-preserving permutations;
a strict adjacent increase would decrease that sum. Equal exponents already
satisfy the required weak order and require no swap.

## The common output and its block matching

Define `e` using precisely the shape and blocks of `d.permute σ`.
The original strong head witnesses supply irreducibility, `hblock` supplies
the analytic field, and the selected `u (σ i)` supply the exponent data and
positive forms. The sorting conclusion is the `antitone` field. Thus all
fields concern these same supplied permuted blocks.

The invariant supplies `Nonempty (d.induced ≅ e.induced)`. The required
bijection from original positions to output positions is `σ.symm`.
`SegmentProductDatum.permute_occurrences` uses `σ (σ.symm i) = i` to give
each dependent degree equality and the transported identity block
isomorphism. Both the product isomorphism and this matching refer to the
single constructed `e`. The positive ambient-rank hypothesis is retained in
the exact target; the construction obtains every output shape field from
`d` and its permutation.

## Dependencies and provenance

This is an internal assembly of published Library results. The exact
interface and its literature motivation are recorded in
[the target's companion Markdown](OrderedSegmentSquareIntegrableConversionStatement.md).
The proof route is the analytic block construction, linkage comparison and
finite invariant-preserving sorting described above.

The analytic input is `SegmentSpecialEssentialSquareIntegrabilityProof`
(Worker 389), unitarity is `SquareIntegrableUnitarityProof` (Worker 438),
and comparison is `LinkedSegmentHeadExponentProof` (Workers 485, 167 and 252).
Each companion Markdown records its own analytic, scalar-norm and source
conventions. The proof uses these exact published theorems at their required
independent universe instances.

`AdjacentUnlinkedSegmentSwapProof` (Worker 584) supplies the full-product
isomorphism. Its independent two-factor input (Worker 375) proves commutation
by irreducibility and contragredient reversal. The shared lifting construction
(Workers 769 and 584) uses exact ordered-product regrouping over a common
merged outer shape, retaining the actual blocks. This conversion uses the
published full-product theorem directly.

The finite sorting proof and the permutation/occurrence constructions are
published support results by Worker 17. Their use retains both the full
product and every original block. The input closures were checked for
independence from this conversion and the downstream exhaustion,
classification, ordered-head existence and quotient-coverage conclusions.
The generic-uniqueness and regular-exhaustion proposition definitions occur
in inherited statement modules; neither is supplied or used as a proved
input. The implemented proof constructs square-integrable Langlands data
and its product isomorphism; it does not construct a head of the full product
or assert exhaustion or classification.
