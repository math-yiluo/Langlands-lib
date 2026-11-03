# Products of unlinked segment socles are irreducible

Author: Worker 758.

This module proves the published proposition
`Langlands.Classification.UnlinkedSegmentSocleProductIrreducible` of
[SegmentSocleCriterionHalvesStatement](SegmentSocleCriterionHalvesStatement.md):
the implication (2)⇒(1) of Zelevinsky (1980), Theorem 4.2. The theorem is
`Langlands.Classification.unlinkedSegmentSocleProductIrreducible`. Its outer
telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, and its type is exactly the proposition, with
independent field and carrier universes `uF` and `uV`.

The statement is unchanged. For every `n` and every datum
`d : T.SegmentProductDatum (n + 1)` whose blocks are segment socles `⟨Δ_i⟩`
(`d.HasSegmentSocles`) and whose multisegment, counted with multiplicity and
in any order, is unlinked, the actual upper normalized induction `d.induced`
is irreducible.

## Route

The proof follows Ze80 §4.3 (printed p.184): induction on the degree through
the highest derivative of the product. Fix a nontrivial unitary additive
character `ψ` (from the existence theorem cited below) and write `D_k` for the
published derivative functor
`Derivative.generalLinearDerivative.{uF, max uF uV} T ψ N k hk`. Let
`λ = ∑ i, rank Δ_i`.

The conditional theorem
`UnlinkedSegmentSocleProductIrreducibleProof.of_derivatives` derives the
target from three published propositions:

- `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement F T`, the
  existence of `ψ`;
- `NonjuxtaposedSegmentSocleDerivativeStrictMono` ((e) of
  [SegmentSocleDerivativesStatement](SegmentSocleDerivativesStatement.md), the
  lattice form of Ze80 Proposition 4.3): if no two segments are juxtaposed, then
  `K₁ < K₂` among subrepresentations of `d.induced` implies a strict inclusion
  of the images of `D_λ` applied to the two inclusions;
- `SegmentSocleProductHighestDerivative` ((f) of the same module): `D_λ(d.induced)`
  is isomorphic to `d'.induced`, where the segments of `d'` are the `Δ_i⁻`
  (the end dropped, original order, singletons omitted), `d'` again has segment
  socles, and `D_λ(d.induced)` is one-dimensional when every segment is a
  singleton.

The main theorem applies `of_derivatives` to the published proofs of these
three propositions.

### The induction

`of_derivatives` proves, by strong induction on `N`, that for every datum `d` of
degree `N` with at least one segment the conclusion holds. A datum of degree
`n + 1` has at least one segment (`length_pos_of_degree`, from
`d.degree_sum`). Since `rank Δ ≤ degree Δ`, `λ ≤ N`, and `λ > 0` because each rank
is positive.

1. **The highest derivative is irreducible.** If every segment is a singleton,
   `D_λ(d.induced)` is one-dimensional by (f), so it is irreducible
   (`isIrreducible_of_finrank_eq_one`: a subspace of a one-dimensional space
   has dimension `0` or `1`). Otherwise some `Δ_i` has length at least `2`.
   Then `Δ_i⁻` is a segment of `d'`, so `d'` has at least one segment, and its
   degree `N - λ` is smaller than `N`. Its multisegment is unlinked
   (`isUnlinked_of_filterMap_minus`, below). The induction hypothesis makes
   `d'.induced` irreducible. The isomorphism of (f) transports irreducibility
   through `Weil.IsomorphismInvariance.irreducible_iff` and
   `SmoothRep.equivOfIso`.
2. **The product is nonzero.** Each block is irreducible, hence nonzero
   (`nontrivial_of_isIrreducible`). The Library lemma
   `RegularHeadExistence.nontrivial_normalizedProductInduction` then makes
   `d.induced` nonzero, so its subrepresentation lattice has `⊥ ≠ ⊤`
   (`subrepresentation_nontrivial`).
3. **No two segments are juxtaposed.** Juxtaposed segments are linked (the
   Library's `IsJuxtaposed` is linkage together with disjoint supports), and
   the multisegment is unlinked, so `Δ_i` and `Δ_j` are not juxtaposed for
   `i ≠ j`.
4. **Conclusion.** Suppose `⊥ < K < ⊤` for some subrepresentation `K`. By (e)
   applied to `⊥ < K` and to `K < ⊤`, the image of `D_λ` of the inclusion of
   `K` lies strictly between the image for `⊥` and the image for `⊤`. In the
   irreducible `D_λ(d.induced)` this image is `⊥` or `⊤`. In the first case the
   image for `⊥` would be strictly below `⊥`; in the second the image for `⊤`
   would be strictly above `⊤`. Both are impossible, so every subrepresentation
   is `⊥` or `⊤`.

### Ze80 4.1: dropping ends preserves unlinkedness

Ze80 §4.1 notes that if `Δ⁻` and `Γ⁻` are linked, so are `Δ` and `Γ`. Here
`Δ⁻ = ⟨Δ.base, Δ.length - 1⟩` keeps the base and drops the end.

- `precedes_of_minus_precedes`: if `Δ⁻` precedes `Γ⁻`, then `Δ` precedes `Γ`.
  The Library's integral-coordinate description of precedence
  (`HasIntegralCoordinates.precedes_iff`, `of_precedes_right`, from
  [SegmentLinkageOrientationProof](SegmentLinkageOrientationProof.md)) needs
  integral-twist freeness of cuspidal data, the published theorem
  `cuspidalIntegralTwistFreeness`. With `ℓ = Δ.length`, place `Δ⁻` at the
  inclusive coordinates `[0, ℓ - 2]` on the twist line of `Δ.base`, and `Γ⁻` at
  `[c, e]`. Precedence of the minus segments is `IntervalPrecedes`:
  `0 < c`, `c ≤ ℓ - 1` and `ℓ - 2 < e`. Then `Δ` sits at `[0, ℓ - 1]` and `Γ`
  at `[c, e + 1]`, and `0 < c`, `c ≤ ℓ` and `ℓ - 1 < e + 1` give precedence
  of `Δ` and `Γ`.
- `isLinked_of_minus_isLinked`: linkage is precedence in one of the two
  orders (`IsLinked.precedes_or_precedes`).
- `isUnlinked_of_filterMap_minus`: if the segments of `d'` are the `Δ_i⁻` of the
  segments of length at least `2` of an unlinked `d`, then `d'` is unlinked.

## Dependency audit

Direct imports:

- the target statement module `SegmentSocleCriterionHalvesStatement`;
- the statement module `SegmentSocleDerivativesStatement` (definitions (b)–(f),
  importing `SupercuspidalDerivativesStatement` with (a));
- `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof`: the theorem
  `padicUnitaryAdditiveCharacterExists` (task 2dbce78d, artifact 72e1678f). Its
  `Langlands` import closure is `HarmonicAnalysis.Basic`,
  `HarmonicAnalysis.CharacterTransport`, `LocalField.Definitions` and its statement
  module, with no representation theory;
- `SegmentIntervalLinkage`, `SegmentLinkageOrientationProof`,
  `CuspidalIntegralTwistFreenessProof`: segment combinatorics;
- `RegularLanglandsHeadReduction`: `nontrivial_normalizedProductInduction`;
- `Weil.Representation.IsomorphismInvarianceProof`: transport of irreducibility;
- `SegmentSocleProductHighestDerivativeProof`: the theorem
  `segmentSocleProductHighestDerivative`, which proves (f) (task 4e152d19,
  artifact cf12542e, Library 286dd3b7). Its import closure has 1202 `Langlands`
  modules;
- `NonjuxtaposedSegmentSocleDerivativeStrictMonoProof`: the theorem
  `nonjuxtaposedSegmentSocleDerivativeStrictMono`, which proves (e) (task
  6c126713, artifact f95b4d5e, Library 428fa7c0). Its import closure has 1299
  `Langlands` modules. Beyond the closure of (f), it adds the proof of (d)
  (`NonjuxtaposedSegmentSocleConstituentLevelProof`, task 60b25b28), the proof of
  (c) (`HighestDerivativeSupportShiftProof`), finite length of products of
  irreducible representations (`IrreducibleProductFiniteLengthProof`, task
  0717fd42, with its Renard finiteness, cuspidal-support and parabolic-induction
  inputs), and the generic helpers `Category.FiniteLengthHelpers`. The Markdown of
  that proof records the same exclusions as this task, including this task and
  its consumers, and finds none of them used.

The import closure of the current imports in the Library (24243ad1) has 1309
`Langlands` modules. A search of these modules for the excluded propositions, and
for their lowercase theorem names, finds proposition definitions in statement modules and unused conditional
assemblies. Examples of the statement-only matches are:

- `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion` and
  `SquareIntegrableLanglandsClassification` in
  `MultisegmentClassificationStatement`;
- `TemperedBlockUniqueness` in `TemperedBlockStatement`;
- the two other halves `LinkedSegmentSocleReverseProductStructure` and
  `LinkedSegmentSoclePairReducible` in the target statement module.

The closure contains no proof of `SegmentSocleProductIrreducibility`,
`AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`,
`LinkedSegmentSocleGluing`, `OrderedMultisegmentSocleExistence`, the
segment-head criterion `SegmentHeadProductIrreducibility`, or the other
excluded tasks. The matching theorem names include the following unused
conditional or boundary results: `multisegmentSocleExhaustion_rankZero` in `SegmentSocleProductData` is the
rank-zero base case in a definitions module, and
`squareIntegrableLanglandsHeadExistence_of_grouping` in
`OrderedMultisegmentHeadReduction` is a conditional assembly that takes its
inputs as hypotheses. The same module also contains the unused conditional
assemblies `orderedMultisegmentHeadExistence_of_conversion` and
`orderedMultisegmentHeadExistence_of_prerequisites`; their internal uses stay
within that unused assembly. `HeadQuotientCriterionProof`, reached through
`RegularLanglandsHeadReduction`, is a general two-quotient lattice lemma, not
the excluded segment-head criterion.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with
declaration `Langlands.Classification.unlinkedSegmentSocleProductIrreducible`:
0 errors, 0 warnings; axioms `propext`, `Classical.choice`, `Quot.sound`.

The nonzero-carrier step reuses
`Langlands.CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible`,
already available through the imported proof infrastructure.
