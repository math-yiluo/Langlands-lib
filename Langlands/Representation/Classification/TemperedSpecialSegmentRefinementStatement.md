# Tempered Langlands data refined into ordered special segments

Authors: Worker 19 (formalization and documentation), Worker 391 (interface
specification).

`Langlands.Classification.TemperedSpecialSegmentRefinement.{uF,uV} F T`
is a proposition-valued definition. It states an internal refinement interface
for positive-rank tempered Langlands data. This module supplies no proof.

## Exact content

The outer parameters are exactly `{p : Nat} [Fact p.Prime]`,
`F : PadicField.{uF} p`, and `T : F.TopologicalData`. With `T.topology`
installed, the proposition says that for every `n : Nat` with `0 < n` and
every `t : T.TemperedLanglandsDatum.{max uF uV,uF} n`, there is
`d : T.SegmentProductDatum.{max uF uV,uF} n` such that

```text
d.IsPrecedenceOrdered ∧ d.HasSegmentHeads ∧
  Nonempty (d.induced ≅ t.standardModule).
```

The field universe `uF` and carrier parameter `uV` are independent. Put
`v = max uF uV`. The input's individual tempered blocks have carriers in
`Type v`, exactly the universe accepted by the published
`TemperedBlockExhaustion.{uF,uV} F T` interface. Applying that interface in a
future proof requires no lowering of carrier universes. The output's segment
representatives and blocks also have carriers in `Type v`, and both induced
objects remain in that universe since `max uF v = v`.

The input datum contains an actual positive block shape summing to `n`,
irreducible analytically tempered smooth complex blocks, and strictly
decreasing real determinant-twist exponents. Its `standardModule` is
normalized induction of those twisted blocks. The output contains actual
segments, their degree-sum equality with `n`, and smooth complex
representations of the corresponding general linear groups.
`d.IsPrecedenceOrdered` says that no earlier segment precedes a later one.
`d.HasSegmentHeads` requires each block to satisfy the strong
`T.IsSegmentHead` relation: an irreducible surjective image of its segment
induction, with uniqueness of the irreducible quotient kernel. It does not
merely record a segment label or a weak constituent relation.

The isomorphism is between actual objects of
`SmoothRep ℂ (GeneralLinear n F.Carrier)`, not between formal parameters or
Grothendieck classes. Both sides use the published normalized product
induction from the standard upper block parabolic, with positive
half-modulus covariance and right translation. The twist is `ν^s` with
`ν = |det|_F` and the residue-normalized absolute value.

The proposition starts with an existing tempered datum. It has no arbitrary
irreducible input representation, full-product head or quotient condition,
extra analytic or classification premise, or assumed factorization.
It exposes only the ordered output datum and the full-product isomorphism;
refinement index maps and chosen normalization exponents are not part of
the interface. Rank zero is outside its quantifiers.

## Internal provenance and future proof

This interface is a derived decomposition step for quotient coverage, not a
verbatim theorem from the literature. Its contextual source is F. Rodier,
*Représentations de GL(n,k) où k est un corps p-adique*, Astérisque 92–93
(1982), §4.3, Theorem 3(c) and Propositions 11–12, printed pp.211–212
(one-based PDF pp.12–13). These pages were read for this pair. The retained
registered source is `rodier-1982-gln`, SHA-256
`389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.
Theorem 3(c) concerns irreducible quotient coverage; it is contextual
motivation, not a proof input to this upstream refinement. Propositions
11–12 supply the stated square-integrable and tempered source route.

An independent proof is intended to perform the following steps, none of
which is implemented or assumed by this proposition definition:

1. Exhaust each untwisted irreducible tempered parent block by an actual
   normalized product of irreducible square-integrable unitary blocks.
2. Transport the parent's real determinant twist through this normalized
   induction. The resulting factors are essentially square-integrable.
   Square-integrability and unitarity are properties of the normalized
   untwisted factors; arbitrary real twists need not preserve either.
3. Identify each resulting factor as an actual special-segment head, using
   the per-block essentially square-integrable classification with strong
   head uniqueness and the necessary rank transports.
4. Prove that each refined head has its parent's real unitary exponent.
   Use the implication that segment precedence forces strictly increasing
   head exponents. In the order obtained by keeping each parent's factors
   consecutive, exponents are equal within a parent and strictly decrease
   between parents, excluding precedence in both cases. `StrictAnti` on
   parent indices alone does not establish this ordering.
5. Flatten the normalized products and construct the full isomorphism, with
   proved associativity and all rank-sum transports.

The published companions
[TemperedBlockStatement](TemperedBlockStatement.md) and
[SegmentSquareIntegrabilityStatement](SegmentSquareIntegrabilityStatement.md),
and the [classification source audit](../../../notes/henniart/gln-classification-sources.md),
retain the source and proof boundaries: Rodier cites Bernstein's unpublished
converse and Jacquet for tempered exhaustion, while Jacquet's unitary
induction result does not itself prove that exhaustion. The later converse
route has separate duality and classification obligations. Citing those
interfaces does not provide proofs of them.

The eventual proof must remain independent of ordered special-segment
quotient coverage, multisegment exhaustion, square-integrable exhaustion,
and regular exhaustion. Any shared lower-level result used in it needs an
acyclic dependency check. This statement imports only
`Langlands.Representation.Classification.LanglandsData` and reuses its
published definitions; it changes no existing Lean/Markdown pair.
