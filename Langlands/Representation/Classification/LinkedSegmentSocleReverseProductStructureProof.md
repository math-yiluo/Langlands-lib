# Zelevinsky 1980 Proposition 4.6 for a linked pair of segment socles

Module `Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStructureProof`,
namespace `Langlands.Classification`.

## Statement proved

`linkedSegmentSocleReverseProductStructure {p : ℕ} [Fact p.Prime]
(F : PadicField.{uF} p) (T : F.TopologicalData) :
LinkedSegmentSocleReverseProductStructure.{uF, uV} F T`.

The proposition is published in
`Classification.SegmentSocleCriterionHalvesStatement`, and its Markdown gives the
precise meaning. The universes `uF` and `uV` are independent. With
`letI := T.topology`, take a datum `d : T.SegmentProductDatum.{uV, uF} n` of
length two with segment socles, `Δ = d.segments 0` and `Δ' = d.segments 1`, and
`Δ'.Precedes Δ`. The proposition then gives:

- the union `U` and the optional intersection `I` of the replacement
  `Δ.IsUnionIntersectionReplacement Δ' U I`;
- a datum `e` with segments `U :: I.toList` and segment socles, whose induced
  representation `ω` is irreducible;
- a two-step filtration `s` of `π = d.induced.representation` with simple
  factors, its top factor isomorphic to `ω` and its bottom factor not
  isomorphic to `ω`;
- the fact that every irreducible subrepresentation of `π` equals
  `s.subrepresentation 1`.

This is Zelevinsky, *Induced representations of reductive p-adic groups II*
(1980), Proposition 4.6 (printed pp.185–186), for `π = ⟨Δ⟩ × ⟨Δ'⟩` and
`ω = ⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩`, with the intersection omitted when the segments are
juxtaposed.

## Proof

The proof is one term. It applies the conditional theorem
`linkedSegmentSocleReverseProductStructure_of` of
`Classification.LinkedSegmentSocleReverseProductConditional` (ported together
with this module) to seven published theorems, one for each of its hypotheses:

| Hypothesis | Published theorem | Module |
| --- | --- | --- |
| `hψ` | `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T` | `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof` |
| `hex` | `segmentZelevinskyConstituentExistence F T` | `Classification.SegmentZelevinskyConstituentExistenceProof` |
| `hirr` | `unlinkedSegmentSocleProductIrreducible F T` (Ze80 Theorem 4.2, (2)⇒(1)) | `Classification.UnlinkedSegmentSocleProductIrreducibleProof` |
| `hA` | `juxtaposedSegmentSocleReverseProductStructure F T` (step (1)) | `Classification.JuxtaposedSegmentSocleReverseProductStructureProof` |
| `hB` | `linkedSegmentSocleReverseProductQuotientHom F T` (step (2)) | `Classification.LinkedSegmentSocleReverseProductQuotientHomProof` |
| `he` | `nonjuxtaposedSegmentSocleDerivativeStrictMono F T` (lattice form of Ze80 4.3) | `Classification.NonjuxtaposedSegmentSocleDerivativeStrictMonoProof` |
| `hf` | `segmentSocleProductHighestDerivative F T` (highest derivative of a product of socles) | `Classification.SegmentSocleProductHighestDerivativeProof` |

Each theorem has the outer telescope `{p} [Fact p.Prime] (F) (T)` and is used at
the same `F`, `T` and universes `uF, uV`, so its type is exactly the hypothesis.
The statements of the hypotheses `hA` and `hB` are in
`Classification.LinkedSegmentSocleReverseProductStepsStatement`. The statements of
`he` and `hf` are in `Classification.SegmentSocleDerivativesStatement`.

The Markdown of the conditional module describes the argument. It follows the
source: step (1) is the juxtaposed case; step (2) is a nonzero map `π → ω`;
step (3) is strong induction on the degree through the highest derivative.

## Dependency audit

Direct imports: the conditional module and the seven proof modules above. The
conditional imports the target statement module, the statement modules of the
inputs, `Classification.CuspidalIntegralTwistFreenessProof`, and the three helper
modules `Filtration.FunctorLengthTwoDetection`,
`Classification.SegmentPrecedenceTruncation` and
`Classification.SegmentSocleProductComparison`. The helpers were written for
this proof.

Import closure. Following the `import` lines transitively, this module has 1373
`Langlands` modules in its closure. The union of the closures of the seven input
proof modules has 1367. The only six other modules are this module, the
conditional module, the three helper modules, and
`Classification.SegmentInitialTruncation`. That last module
defines the one-step truncation `Segment.dropLastNonempty`/`Segment.dropLast` and
imports only `Classification.Segments`. So no module in the closure lies outside
the input proofs except definitions and lemmas written for this proof and one
segment-combinatorics definitions module.

The seven inputs are published proofs. The Markdown of each records its own
dependency audit. The audits of `hirr`, `hA` and `hB` check independence from
the excluded results listed below and from this target or its proof. In
particular, none of the inputs uses
`LinkedSegmentSocleReverseProductStructure`.

Name search. Every module of the closure was searched for the excluded
propositions, written both capitalized and lowercase (that is, also as their
proof theorem names). The names are:

- `LinkedSegmentSoclePairReducible`;
- `SegmentSocleProductIrreducibility`;
- `AdjacentUnlinkedSegmentSocleSwap`;
- `TwoSegmentSocleCommutation`;
- `LinkedSegmentSocleGluing`;
- `OrderedMultisegmentSocleExistence`;
- `MultisegmentSocleExhaustion`;
- `SegmentEssentialSquareIntegrableClassification`;
- `MultisegmentHeadExhaustion`;
- `OrderedMultisegmentHeadExistence`;
- `OrderedMultisegmentQuotientExhaustion`;
- `TemperedBlockUniqueness`;
- `SquareIntegrableLanglandsClassification`;
- `SquareIntegrableLanglandsExhaustion`;
- `GLRegularLanglandsExhaustion`;
- `SegmentHeadProductIrreducibility`.

No proof module of any of these is in the closure. The matches are:

- proposition definitions in statement modules:
  `MultisegmentClassificationStatement` defines `MultisegmentSocleExhaustion`,
  `MultisegmentHeadExhaustion`, `OrderedMultisegmentSocleExistence`,
  `OrderedMultisegmentHeadExistence`, `SquareIntegrableLanglandsExhaustion` and
  `SquareIntegrableLanglandsClassification`; `TemperedBlockStatement` defines
  `TemperedBlockUniqueness`; `RegularLanglandsStatement` defines
  `GLRegularLanglandsExhaustionStatement`; the target statement module defines
  `LinkedSegmentSoclePairReducible`. Outside these statement modules, an
  excluded name occurs in the closure only in the next two items;
- `multisegmentSocleExhaustion_rankZero` in `Classification.SegmentSocleProductData`,
  a rank-zero lemma in a definitions module;
- `orderedMultisegmentHeadExistence_of_conversion` and
  `orderedMultisegmentHeadExistence_of_prerequisites` in
  `Classification.OrderedMultisegmentHeadReduction`, conditional assemblies that
  take their inputs as hypotheses. Their conclusion is
  `OrderedMultisegmentHeadExistence`; no module of the closure uses them;
- the target name `LinkedSegmentSocleReverseProductStructure`, which occurs only in
  the target statement module, in doc comments of
  `LinkedSegmentSocleReverseProductStepsStatement`, in the conditional module
  and in this module.

`LinkedSegmentSoclePairReducible` and its proof are not used.

## Checks

`lean_check`, with declaration `Langlands.Classification.linkedSegmentSocleReverseProductStructure`:
0 errors, 0 warnings. The axioms are `propext`, `Classical.choice` and
`Quot.sound`.
