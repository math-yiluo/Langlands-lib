# Proof of the two-block Jacquet formula for segment socles

Author: Worker 756.

This module proves the published proposition
`Langlands.Classification.SegmentSocleJacquetFormula` from
[`SegmentSocleJacquetStatement`](SegmentSocleJacquetStatement.md), which states
Zelevinsky 1980, Proposition 3.4 (printed pp.181–182). The theorem is

```lean
theorem Langlands.Classification.segmentSocleJacquetFormula
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentSocleJacquetFormula.{uF, uV} F T
```

It holds for every prime `p`, every `F` and every `T`, with independent universes
`uF` and `uV` and no further hypotheses. For a segment `Δ` of length `m`, cuspidal
rank `r` and degree `n = m r`, and every `π` with `T.IsSegmentSocle Δ π`, it gives
both clauses of the target:

1. the normalized Jacquet module of `π` along `(l, n - l)` is zero when `r ∤ l`;
2. for every `0 < q < m` there are actual socles `π₁` of `Δ.initial q hq` and `π₂`
   of `Δ.terminal q hqm` such that the normalized Jacquet module of `π` along
   `Δ.socleSplitShape q hq hqm = (q r, (m - q) r)` is isomorphic to the external
   tensor product `π₁ ⊠ π₂`.

## Implemented proof

The proof applies the supporting lemma
`SegmentSocleJacquetReduction.segmentSocleJacquetFormula_of` from
[`SegmentSocleJacquetReduction`](SegmentSocleJacquetReduction.md), which ships with
this candidate. That lemma derives the target for one `F` and `T` from four
propositions. Here each of them is supplied by a theorem published in the Library
(checked at commit `fcac121256163a8da6dd01a9483e1104a9b92aba`):

- **H1**, `Classification.SegmentSubrepresentationFullJacquet.{uF, uV} F T`
  (Zelevinsky 1980, 3.1, for segment subrepresentations): the first conjunct of
  `Langlands.Classification.segmentFullJacquetFormula F T` from
  [`SegmentFullJacquetProof`](SegmentFullJacquetProof.md). Its type is
  `SegmentFullJacquetFormula F T`, the conjunction of
  `SegmentSubrepresentationFullJacquet` and `SegmentQuotientFullJacquet`. Only the
  first conjunct is used.
- **H2**, `CuspidalSupport.NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n`
  for every `n` (Bernstein–Zelevinsky 1977, Corollary 2.13(b)):
  `Langlands.CuspidalSupport.nonassociatedJacquetSubquotients F T n` from
  [`NonassociatedJacquetSubquotientsProof`](../CuspidalSupport/NonassociatedJacquetSubquotientsProof.md).
- **H3**, `Classification.SegmentZelevinskyConstituentExistence.{uF, uV} F T`
  (existence of segment socles):
  `Langlands.Classification.segmentZelevinskyConstituentExistence F T` from
  [`SegmentZelevinskyConstituentExistenceProof`](SegmentZelevinskyConstituentExistenceProof.md).
- **H4**, `CuspidalSupport.CuspidalInductionLengthTheorem.{uF, uV} F T n` for every
  `n` (Bernstein–Zelevinsky 1977, Theorem 2.8, finite length of irreducible cuspidal
  induction): `Langlands.CuspidalSupport.cuspidalInductionLength F T n` from
  [`NormalizedCuspidalInductionLengthProof`](../CuspidalSupport/NormalizedCuspidalInductionLengthProof.md).

The universes match those of the target: each input is used at `{uF, uV}` for the
same `F` and `T`.

The supporting module proves the two clauses as follows; its Markdown has the
details.

- **Clause 1.** Write `I` for the segment induction of a supercuspidal
  representative `A` of the base, which contains `π`. If the Jacquet module of `π`
  along `C = (l, n - l)` is nonzero, the published `minimalNonzeroRefinedJacquet`
  gives a refinement `S` of `C` with a nonzero quasicuspidal refined Jacquet module.
  That module is a subquotient of the Jacquet module of `I` along `C.flatten S`. H2
  then forces `C.flatten S` to be associated with the uniform shape `(r, …, r)`, so
  every block has size `r` and `r ∣ l`.
- **Clause 2.** H3 supplies socles `π₁` and `π₂` of `Δ.initial q hq` and
  `Δ.terminal q hqm`. Induction in stages and the published embedding of products of
  factor embeddings give an injection `π₁ × π₂ ↪ I`. `I` has finite length by H4,
  and `π` is the irreducible socle of `I`, so `π` maps nontrivially into `π₁ × π₂`.
  Frobenius reciprocity (`Parabolic.FirstAdjointness.equiv`) turns this map into a
  nonzero map from the Jacquet module of `π` along `(q r, (m - q) r)` to the
  irreducible `π₁ ⊠ π₂`, so the map is surjective. By H1 the Jacquet module of `π`
  along `(r, …, r)` is irreducible. With H2, this makes the surjection injective.

All objects are the actual ones of the target: the actual normalized Jacquet
functors, actual normalized parabolic induction and the actual external tensor
functor. The existential clause is witnessed by the socles that H3 actually
constructs, not by an assumption that they exist.

## Relation to the source route

Zelevinsky computes the two-block Jacquet module through the Jacquet module of an
external tensor product (his 1.5(a)) and then recognizes the factors by 3.1 for the
shorter segments. The Lean proof avoids 1.5(a) and that recognition. It maps onto the
given `π₁ ⊠ π₂` by Frobenius reciprocity and proves injectivity from H1 and H2. For
clause 1 it uses BZ77 2.13(b) where the source cites 2.13(a) or Ze80 1.6.

## Dependencies and independence

The proof assumes no derivative formula and no product irreducibility criterion. It
quotes neither Proposition 3.4 nor an exponent norm bound. Every input is a proved,
published theorem.

Independence from the excluded results was checked as follows (at workspace base
`fcac1212`):

- **Module level.** The import closure of this module has 1122 `Langlands` modules.
  None of them is a proof module of, or mentions a conclusion of, the excluded results:
  - `SegmentSocleProductIrreducibility` (task 2ae5cbe5);
  - adjacent socle commutation `AdjacentUnlinkedSegmentSocleSwap` (e3634665);
  - `OrderedMultisegmentSocleExistence` (23189526);
  - `MultisegmentSocleExhaustion` (f3a69bc8);
  - `SegmentEssentialSquareIntegrableClassification` (aca8805b);
  - `MultisegmentHeadExhaustion` (3bfb61fa);
  - `OrderedMultisegmentHeadExistence` (ebea9a8a);
  - `OrderedMultisegmentQuotientExhaustion` (20e4e1c6);
  - `TemperedBlockUniqueness` (52e97845);
  - `SquareIntegrableLanglandsClassification` (1cb45da2);
  - `SquareIntegrableLanglandsExhaustion` (cd8ab97c);
  - `GLRegularLanglandsExhaustionStatement` (bf433f0a);
  - `SegmentHeadProductIrreducibility` (8364e73f).

  The one exception is the statement module `RegularLanglandsStatement`, which
  only defines the proposition `GLRegularLanglandsExhaustionStatement`.
- **Constant level.** All constants reachable from the types and values of
  `segmentSocleJacquetFormula` were collected: 90 963 constants, 12 106 of them in
  `Langlands`. None of them is, or has a name containing, any declaration listed
  above or its theorem-name counterpart. The proposition
  `GLRegularLanglandsExhaustionStatement` is not among them.
- **Shared lower inputs.** The supporting module uses
  `RegularHeadExistence.nontrivial_normalizedProductInduction` from
  `RegularLanglandsHeadReduction`. That theorem is unconditional: normalized
  product induction of nontrivial blocks is nontrivial. The constant-level check
  shows that it does not depend on regular exhaustion. From the head-side statement
  module `SegmentHeadJacquetStatement`, only the definitions `Segment.initial` and
  `Segment.terminal` of the target are used, not the head Jacquet conclusion of task
  55ad1e10.
- The derivative results (Bernstein–Zelevinsky derivatives, Leibniz filtrations) and
  the two-supercuspidal product irreducibility `TwoSupercuspidalNonadjacentIrreducibilityProof`
  in the closure enter only through the published proofs of H1 and H3. They are
  proved lower results, not hypotheses, and are none of the excluded multisegment
  criteria.

## Provenance

Statement: Zelevinsky 1980, Proposition 3.4, printed pp.181–182 (source
`zelevinsky-1980-induced-ii`), as stated in the Library's
`SegmentSocleJacquetStatement`. The proof route is internal, as described above. It
uses Bernstein–Zelevinsky 1977 (source `bernstein-zelevinsky-1977-induced-i`),
Corollary 2.13(b) and Theorem 2.8, and Zelevinsky 1980, 3.1, through their published
Library theorems.
