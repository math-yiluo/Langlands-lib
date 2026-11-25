# Proof of the segment socle irreducibility criterion

## Statement proved

`Langlands.Classification.segmentSocleProductIrreducibility` proves exactly
`Langlands.Classification.SegmentSocleProductIrreducibility.{uF, uV} F T` from
`Classification.SegmentGenericStatement`, with the outer telescope
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)` and no
further hypotheses. Under `T.topology`, for every `n` and every
`d : T.SegmentProductDatum.{uV, uF} (n + 1)` with segment socles,
`d.induced.representation` is irreducible if and only if `d.multisegment` is
unlinked (Zelevinsky 1980, Theorem 4.2, printed p. 184).

## Proof

The theorem is `SegmentSocleCriterionAssembly.segmentSocleProductIrreducibility_of_halves`
(helper module `Classification.SegmentSocleCriterionAssembly`, published together
with this proof; see its Markdown for the full argument) applied to:

- `unlinkedSegmentSocleProductIrreducible F T`, the published proof of
  `UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T` (sufficient direction,
  Ze80 4.2 (2)⇒(1));
- `linkedSegmentSoclePairReducible F T`, the published proof of
  `LinkedSegmentSoclePairReducible.{uF, uV} F T` (a linked pair of segment socles
  gives a reducible product, both orders; Ze80 4.6);
- `twoFactorProductConstituentCommutativity.{uF, max uF uV} F T`, the published
  proof of the irreducible two-factor case of Ze80 Theorem 1.9, at the carrier
  universe `max uF uV` of the blocks.

The helper module proves the necessary direction by induction on the distance
between two positions: adjacent linked socles make the merged two-block factor,
hence the whole product, reducible; adjacent unlinked socles commute up to
isomorphism (both orders irreducible by the sufficient direction, same
Jordan–Hölder factors by Theorem 1.9), so a linked pair at larger distance can be
moved together.

## Dependency audit

Direct imports:

- `Classification.SegmentSocleCriterionAssembly`, the helper module published
  together with this proof. Its own imports are the target statement module
  `Classification.SegmentGenericStatement`, the halves statement module
  `Classification.SegmentSocleCriterionHalvesStatement`, the statement module
  `Classification.TwoFactorProductConstituentCommutativityStatement`,
  `Classification.SegmentProductPermutation`,
  `Parabolic.OrderedProductRegroupingProof`,
  `Parabolic.ProductInductionSubrepresentation`, `Filtration.RepresentationLength`
  and `Filtration.LengthTwoMatching`. It takes the three propositions below as
  hypotheses and calls no other analytic result;
- `Classification.UnlinkedSegmentSocleProductIrreducibleProof`;
- `Classification.LinkedSegmentSoclePairReducibleProof`;
- `Classification.TwoFactorProductConstituentCommutativityProof`.

Here `Classification`, `Parabolic` and `Filtration` abbreviate the corresponding
namespaces under `Langlands.Representation`.

The `Langlands` import closure of this module has 1380 modules. The closure of
the proof of `LinkedSegmentSoclePairReducible` has 1377 modules and contains the
closures of the other two proofs (1311 and 558 modules) and every import of the
helper module except `SegmentGenericStatement`. The closure of this module adds
exactly three modules to it: the target statement module `SegmentGenericStatement`,
the helper module, and this module. `SegmentGenericStatement` imports only
`Classification.LanglandsData`, `Classification.SegmentConstituentStatement` and
`Whittaker.GeneralLinear`, which already lie in that closure; it defines the
target `SegmentSocleProductIrreducibility`, the segment-head proposition
`SegmentHeadProductIrreducibility` and their conjunction, with no proofs. Every
module of the closure other than the three new ones and the proof of
`LinkedSegmentSoclePairReducible` is byte-identical (Lean and Markdown) in Library
commit 25b91125, where the input proofs were audited, and in commit 622054b9, the
base of this proof. The published proof of `LinkedSegmentSoclePairReducible`
in 622054b9 is byte-identical to its audited version.

The three input proofs record their own independence audits in their Markdown.
All three avoid every result excluded for this proof, and this proof itself.
The `LinkedSegmentSoclePairReducible` proof also
avoids the proposition `SegmentSocleProductIrreducibility`, the segment-head
criterion `SegmentHeadProductIrreducibility`,
`AdjacentUnlinkedSegmentSocleSwap`,
`TwoSegmentSocleCommutation` and
`LinkedSegmentSocleGluing`. Its audit, whose
closure contains the closures of the other two proofs, inventories the published
proofs of all those excluded results and finds none of their modules in its
closure.

A case-insensitive search of every module in this closure for the excluded
propositions and their theorem names (`SegmentSocleProductIrreducibility`,
`SegmentHeadProductIrreducibility`, `OrderedMultisegmentSocleExistence`,
`SquareIntegrableLanglandsClassification`, socle and head exhaustion, head
existence, quotient coverage, tempered block uniqueness, analytic
classification, `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`,
`LinkedSegmentSocleGluing`) finds only:

- `SegmentSocleProductIrreducibility` in its statement module, in the helper
  module, which assumes only the halves, and in this theorem;
- `SegmentHeadProductIrreducibility` in its statement module, as a definition;
- `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, head
  exhaustion and `SquareIntegrableLanglandsClassification` in
  `MultisegmentClassificationStatement`, and `TemperedBlockUniqueness` in
  `TemperedBlockStatement`, as definitions;
- `GLRegularLanglandsHeadExistenceStatement` in `RegularLanglandsStatement`, as a
  definition, used only as a hypothesis of the conditional assemblies in
  `OrderedMultisegmentHeadReduction` listed below;
- `multisegmentSocleExhaustion_rankZero` in `SegmentSocleProductData`, a
  rank-zero boundary lemma that nothing in the closure calls;
- the conditional assemblies `orderedMultisegmentHeadExistence_of_conversion`,
  `orderedMultisegmentHeadExistence_of_prerequisites` and
  `squareIntegrableLanglandsHeadExistence_of_grouping` in
  `OrderedMultisegmentHeadReduction`, which take their inputs as hypotheses and
  are used only by one another;
- the namespace `RegularHeadExistence` of `RegularLanglandsHeadReduction`, whose
  lemma `nontrivial_normalizedProductInduction` (a normalized product of nonzero
  blocks is nonzero) is used by the proof of `UnlinkedSegmentSocleProductIrreducible`
  and by `SegmentSocleJacquetReduction`.
  That module proves no head existence or exhaustion statement; its head
  constructions take finite length and the absence of product quotients as
  hypotheses.

Hence no excluded conclusion is assumed or proved anywhere in the closure:
socle exhaustion, segment analytic classification,
special-head multisegment exhaustion, ordered special-head existence,
quotient coverage, tempered block uniqueness,
`SquareIntegrableLanglandsClassification`, square-integrable
exhaustion, regular exhaustion,
`OrderedMultisegmentSocleExistence`, the segment-head criterion
`SegmentHeadProductIrreducibility`, `TwoSegmentSocleCommutation`
and `AdjacentUnlinkedSegmentSocleSwap`.

## Checks

`lean_check` with
declaration `Langlands.Classification.segmentSocleProductIrreducibility`:
0 errors, 0 warnings; universe parameters `uF`, `uV`; axioms `propext`,
`Classical.choice`, `Quot.sound`.
