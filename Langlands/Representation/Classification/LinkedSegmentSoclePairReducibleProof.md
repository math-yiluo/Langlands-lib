# Reducibility of a linked pair of segment socles

Authors: Workers 328 and 991. Worker 991 wrote the assembly and its initial
explanation. Worker 328 verified the original source passages, replaced the
conditional inputs by the published proofs, and audited the enlarged import
closure.

The theorem `Langlands.Classification.linkedSegmentSoclePairReducible` proves
exactly the published proposition
`Langlands.Classification.LinkedSegmentSoclePairReducible.{uF,uV} F T`.
Its only parameters are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)` and
`(T : F.TopologicalData)`. For every actual segment-product datum of length two,
segment socles and linkage imply that its normalized induced representation is
not irreducible. Both orders are covered; no precedence premise is imposed.

The proof instantiates two published theorems as local facts:

- `hRev := linkedSegmentSocleReverseProductStructure.{uF,uV} F T`, proving
  Zelevinsky 1980, Proposition 4.6;
- `hComm := twoFactorProductConstituentCommutativity.{uF,max uF uV} F T`,
  proving the irreducible two-factor case of Zelevinsky 1980, Theorem 1.9.

The latter uses carrier universe `max uF uV` because the actual blocks of a
`SegmentProductDatum.{uV,uF}` are `SmoothRep.{0,uF,max uF uV}`. Neither fact is
an additional hypothesis of the theorem.

## Lemma `not_isIrreducible_of_haveSameJordanHolderFactors_lengthTwo`

Let `ρ` be a representation over a field and `B` a representation with a
filtration `t` of length two whose graded pieces are irreducible. If `ρ` and
`B` have the same Jordan–Hölder factors, then `ρ` is not irreducible.

Proof. Suppose `ρ` is irreducible. The witness consists of composition series
`s` of `ρ` and `s'` of `B`, both of some length `m`. Since `⊥ ⋖ ⊤` in the
subrepresentation lattice of an irreducible `ρ` (`bot_covBy_top`), the
filtration `LengthTwo.oneStep ρ`, `0 ⊆ ρ`, has simple factors
(`LengthTwo.oneStep_hasSimpleFactors`). The published comparison
`jordanHolderSeriesComparison` gives bijections `Fin m ≃ Fin 1` (from `s` and
`oneStep ρ`) and `Fin m ≃ Fin 2` (from `s'` and `t`). Their cardinalities give
`m = 1` and `m = 2`, a contradiction.

## Theorem `linkedSegmentSoclePairReducible`

Fix `n`, `d` with `d.length = 2`, segment socles `hs` and linked segments
`Δ = d.segments 0`, `Δ' = d.segments 1`. By `Segment.IsLinked.precedes_or_precedes`
(`Classification.SegmentLinkageOrientationProof`), either `Δ` precedes `Δ'`
or `Δ'` precedes `Δ`.

- `Δ'` precedes `Δ`. `hRev` applied to `d` gives a filtration `s` of
  `Rep.of d.induced.representation` of length two with simple factors. The
  self-matching `haveSameJordanHolderFactors_self s` and the lemma show that
  `d.induced.representation` is not irreducible.
- `Δ` precedes `Δ'`. Let `σ = d.shape.adjacentSwap 0 _` and `d' = d.permute σ`
  (`Classification.SegmentProductPermutation`). Then `d'.segments 1 = Δ` and
  `d'.segments 0 = Δ'` (by `Equiv.swap_apply_right` and `Equiv.swap_apply_left`),
  so `Δ` = `d'.segments 1` precedes `d'.segments 0`, and `d'` has segment socles
  since its blocks are `d.blocks (σ i)`. `hRev` applied to `d'` gives a
  length-two filtration with simple factors of `Rep.of d'.induced.representation`.
  Each block of `d` is irreducible: the first conjunct of
  `IsIrreducibleSocle` inside `IsSegmentSocle`. `hComm n d.shape h₂ d.blocks`
  gives `HaveSameJordanHolderFactors` of `Rep.of d.induced.representation` and
  `Rep.of d'.induced.representation`; both sides are these representations by
  definition (`SegmentProductDatum.induced`, `permute_induced`, `permute_shape`).
  The lemma shows that `d.induced.representation` is not irreducible.

## Parameters and conventions

The theorem has independent universe parameters `uF` and `uV`. Its parameters
are exactly the prime with `Fact p.Prime`, the field `F`, and the supplied
topology datum `T`. It installs `T.topology` before introducing the target's datum. Neither
case changes that topology or the carrier universe of a segment. Only the
commutativity proposition is instantiated at `max uF uV`, the universe of
the actual block carriers. The generic Jordan–Hölder lemma allows independent
carrier universes for its two representations.

The permutation retains the supplied blocks occurrence by occurrence, so
equal blocks or segments introduce no choice of representatives. The argument
uses only the two positions in a datum of length two. Rank zero and rank one
need no separate proof: any impossible datum remains under the unchanged
universal quantifiers. The induction is the original
`normalizedProductInductionFunctor` on the standard upper block parabolic,
with positive half-modulus covariance and right translation. No isomorphism
between the two product orders is assumed; `hComm` supplies actual composition
series with matching factors.

## Original source and implemented route

The registered original is A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*,
Ann. Sci. ENS (4) 13 (1980), pp.165–210, literature ID
`zelevinsky-1980-induced-ii`. The retained PDF has SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Worker 328 verified that fingerprint and read the rendered printed pages
174 and 184–186 (one-based PDF pages 11 and 21–23). No public errata file
`notes/errata/zelevinsky-1980-induced-ii.md` existed in the audited Library.

Section 4.1, p.184, defines linkage and precedence. The proposition in §4.6,
pp.185–186, gives the two irreducible factors in the reverse precedence
order; its last sentence derives the remaining direction of Theorem 4.2.
Theorem 1.9, p.174, identifies the composition factors of the two product
orders. The formal assembly uses the irreducible two-factor specialization
of that theorem. It extracts only the length-two composition series from
§4.6's stronger structure proposition.

The Jordan–Hölder contradiction is a derived algebraic argument, implemented
using the published arbitrary-field, arbitrary-monoid comparison theorem.
It does not repeat the derivative proof of §4.6, or the inverse-transpose
and contragredient proof of Theorem 1.9. Those analytic inputs are supplied by the two
published proofs imported here.

## Dependency audit

The seven direct imports are:

- `Classification.SegmentSocleCriterionHalvesStatement`: the unchanged target
  and reverse-structure proposition definitions;
- `Classification.TwoFactorProductConstituentCommutativityProof`: the published
  proof of actual two-factor constituent commutativity;
- `Classification.LinkedSegmentSocleReverseProductStructureProof`: the published
  reverse-precedence structure proof;
- `Classification.SegmentProductPermutation`: reindexing the actual segments
  and blocks, with definitional identification of the permuted induction;
- `Classification.SegmentLinkageOrientationProof`: finite-support orientation;
- `Filtration.JordanHolderComparisonProof`: comparison of supplied composition
  series of the same representation;
- `Filtration.LengthTwoMatching`: the actual one-step filtration and its
  simple-factor proof from the covering relation `⊥ ⋖ ⊤`.

Here `Classification` and `Filtration` abbreviate the corresponding namespaces
under `Langlands.Representation`. The orientation proof uses distinct bases
inside a segment witnessing the support union and the positive difference of
their indices. It uses no analytic classification premise. Permutation is
reindexing and finite-sum invariance; it supplies no representation commutation
conclusion. The filtration arguments are general module theory: covering pairs,
actual quotient representations, the second isomorphism theorem, and Mathlib's
lattice Jordan–Hölder comparison.

Worker 328 reconstructed all direct and transitive project imports in Library
commit `25b91125ea94e88d741b206d633e82eb0d87c3e5`. The closure contains 1377
project modules, including this one. The reverse-structure proof's closure has
1374 modules and the commutativity proof's closure has 558; their union has
1376. Thus every inherited module is already in the closure of one of those
published proofs. The two modules added to the reverse-structure closure by
commutativity are precisely its statement and proof modules. Every inherited
Lean/Markdown pair matches that Library commit byte for byte. The target
statement and its imported pairs are unchanged.

The proof of reverse structure uses the published nontrivial additive character,
segment constituent existence, unlinked socle irreducibility, juxtaposed
structure, quotient Hom, nonjuxtaposed derivative strict monotonicity, and
product highest derivative proofs. Its substantive conditional assembly and
those input proofs record their own independence audits. The present proof uses
only the resulting length-two series, never a socle criterion or a gluing
conclusion. Commutativity uses inverse transpose, normalized induction duality,
Gelfand–Kazhdan, admissibility, finite length of products of irreducibles, and
Jordan–Hölder transport. In the integrated Library its generic pullback helpers
are shared in `Filtration.FactorMatchingPullback`; that actual module is included
in this audit. Its proof has no segment classification input.

A case-insensitive scan of every source in the enlarged closure for every
excluded proposition and its proof-name spelling gives the following matches,
which were inspected:

- `MultisegmentClassificationStatement`, `TemperedBlockStatement`, and
  `RegularLanglandsStatement` define excluded propositions and conjunctions of
  propositions. These are definitions, not proofs or assumed instances of them.
- `SegmentSocleProductData.multisegmentSocleExhaustion_rankZero` is a boundary
  result about the empty product. There is no call to it anywhere in the
  closure.
- `OrderedMultisegmentHeadReduction` contains the conditional assemblies
  `orderedMultisegmentHeadExistence_of_conversion` and
  `orderedMultisegmentHeadExistence_of_prerequisites`, and the supporting
  `squareIntegrableLanglandsHeadExistence_of_grouping`. Their calls remain
  inside those assemblies; no other closure module calls them. Lower results
  from that module used upstream concern rank zero and one-dimensional carriers.
- The present target occurs only in its original proposition definition and
  this theorem. No inherited proof assumes or invokes it.

In addition, an inventory of the currently published, task-bound proof records
of all eighteen explicitly excluded tasks and proof successors finds no
contributed module in this closure. The seven lower definition modules recorded
by the accepted juxtaposed and quotient-Hom audits as having been authored under
the socle-exhaustion task are `Combinatorics.RelationInversions`,
`Classification.SegmentIntegralCoordinates`, `SegmentIntervalLinkage`,
`SegmentReplacementInversions`, `SegmentUnionIntersection`,
`SegmentProductReplacement`, and `Filtration.ObjectTransport`. They supply
coordinates, interval combinatorics, replacement data and general filtration
transport; their actual source contains no excluded conclusion or assumption.
Several already lie in the target statement's own import closure.
`Classification.Essential` and `Classification.Tempered` likewise supply
analytic property definitions and elementary transport and normalization.
`Classification.HeadQuotientCriterionProof` is a general two-quotient lattice
lemma; it is independent of the excluded segment-head product criterion.

These checks, together with the closed proofs and their inherited audits,
establish direct and transitive independence from the conclusions below.
Shared lower definitions and proofs are used only with that independence.

The complete exclusions carried by this task are:

- `SegmentSocleProductIrreducibility` and task
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`;
- `AdjacentUnlinkedSegmentSocleSwap`, task
  `e3634665-571b-4852-9f4c-bab8a1053434` and proof successor
  `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`;
- `TwoSegmentSocleCommutation` and tasks
  `426911b4-6620-413f-8065-04b25287f3bd` and
  `66e3b87c-647e-41e4-af18-df4d436765f0`;
- `LinkedSegmentSocleGluing` and tasks
  `c84cd52c-3ff3-4024-be50-8b84dd480888` and
  `6780b79c-9526-46aa-b8b4-00377d68b1ea`;
- `OrderedMultisegmentSocleExistence` and task
  `23189526-80b0-4828-a6d4-7ebec2cbeef5`;
- socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`;
- segment analytic classification `aca8805b-054f-4d56-8045-12db7f623404`;
- special-head multisegment exhaustion
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`;
- ordered special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
- quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`;
- tempered block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`;
- `SquareIntegrableLanglandsClassification` and task
  `1cb45da2-7007-4351-a694-594fb148b8d1`;
- square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`;
- regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`;
- `SegmentHeadProductIrreducibility` and task
  `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, including its conclusions.

These exclusions cover mathematical conclusions, proof successors, and
transitive proof dependencies. Shared lower infrastructure is reusable only
after checking that independence.

## Development validation

In the approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
`lean_check` compiled this exact theorem and inspected its declaration with zero
errors and warnings. Its universe parameters are `uF` and `uV`, and its only
axioms are `propext`, `Classical.choice`, and `Quot.sound`. This development
check is separate from the candidate's exact-target validation and independent
semantic review.
