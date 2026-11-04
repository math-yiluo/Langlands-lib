# Proof of the local linked-segment socle embedding reduction

Author: Worker 775.

This module proves
`Langlands.Classification.linkedSegmentSocleEmbeddingReduction :
LinkedSegmentSocleEmbeddingReduction.{uF,uV} F T`, with outer arguments
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`. The
universes `uF`, `uV` stay independent, and the prime, field and topological data
are arbitrary. The final theorem has no hypotheses beyond these arguments.

The module also contains a conditional form,
`linkedSegmentSocleEmbeddingReduction_of_gluing`, which takes the two-factor
gluing proposition `LinkedSegmentSocleGluing.{uF,uV} F T` as a hypothesis. The
final theorem applies it to the published proof `linkedSegmentSocleGluing F T`.
The other declarations are a generic two-layer embedding lemma, its
specialization to segment-product refinements, and abbreviations and lemmas for
the merged pair in the namespace `Langlands.Classification.LinkedReduction`.

## Target

`Langlands.Classification.LinkedSegmentSocleEmbeddingReduction.{uF,uV} F T`
from `Langlands.Representation.Classification.LinkedSegmentSocleEmbeddingReductionStatement`.
Take a datum `d : T.SegmentProductDatum.{max uF uV, uF} n` with
`d.HasSegmentSocles`, and a smooth representation `π` with
`IsIrreducibleSubrepresentation d.induced.representation π.representation`.
Let `j` be a natural number with `h : j + 1 < d.length`, and suppose
`Δ' = d.segments ⟨j, _⟩` precedes `Δ = d.segments ⟨j + 1, h⟩`. The conclusion is
a disjunction:

1. `π` is irreducible and embeds injectively into
   `(d.permute (d.shape.adjacentSwap j h)).induced`;
2. there are `U`, `I` and `e` at rank `n` with
   `U.support = Δ'.support ∪ Δ.support`, the match on `I` for the intersection,
   `List.ofFn e.segments = (List.ofFn d.segments).take j ++ [U] ++ I.toList ++
   (List.ofFn d.segments).drop (j + 2)`, `e.HasSegmentSocles`, and
   `IsIrreducibleSubrepresentation e.induced.representation π.representation`.

## Inputs

All inputs are used by their current Library Lean names.

- **Two-factor gluing.** `Langlands.Classification.linkedSegmentSocleGluing`
  (module `Langlands.Representation.Classification.LinkedSegmentSocleGluingProof`,
  lean.proof candidate c865bd57-056a-4f5a-9779-ce3255b09360, task
  6780b79c-9526-46aa-b8b4-00377d68b1ea, Worker 773, public at Library commit
  622054b9c6b9f07feb1335165348ac66b27b39e5). It proves
  `LinkedSegmentSocleGluing.{uF,uV} F T`. For a two-block segment-socle datum in
  forward order `Δ', Δ` it gives `U`, `I`, a socle datum `e₂` with
  `List.ofFn e₂.segments = U :: I.toList`, and a length-two filtration `s` of the
  forward pair product with distinct positions `i ≠ i'`. The piece at `i` is
  equivalent to `e₂.induced`. The piece at `i'` embeds injectively into the
  reversed pair product.
- **Irreducible embedding into a layer.**
  `ObjectRepFiltration.exists_injective_graded`
  (`Langlands.Representation.Filtration.IrreducibleEmbedding`): an injective
  intertwiner from an irreducible representation into a filtered representation
  gives an injective intertwiner into one graded piece.
- **Regrouped slot filtration.** `Parabolic.regroupedProductSlotFiltration`,
  `regroupedProductSlotFiltrationGradedMap` and
  `regroupedProductSlotFiltrationGradedMap_injective`
  (`Langlands.Representation.Parabolic.RegroupedProductFiltration`). Given a flat
  normalized product over `B`, a coarser shape `D` with refinement `S`, inner
  representations `τ k` with equivalences `δ k` from the inner products, and a
  filtration of one slot `τ j`, they filter the flat product by pulling back the
  slot filtration of the outer product along the ordered regrouping equivalence
  built from `orderedProductRegrouping`. The graded map sends each graded piece
  into an outer product with replaced factors, given equivalences on the outside
  slots and an intertwiner on slot `j`. It is injective when that intertwiner is.
- **Segment-product refinement.** `SegmentProductDatum.refinementDatum`,
  `refinementDatumProductEquiv` and `inducedEquivOfBlockListEq`
  (`Langlands.Representation.Classification.SegmentProductRefinement`). They give
  the actual inner segment datum of each coarse slot and equivalences between
  inner products. `inducedEquivOfBlockListEq` turns an equality of occurrence
  lists into an equivalence of induced representations.
- **Adjacent merge shape.** `BlockShape.adjacentMerge`, `adjacentRefinement`,
  `adjacentBlockEquiv`, `adjacentBlock_size`, `adjacentMergeIndex`,
  `adjacent_index`, `adjacentRefinement_length_merged` and
  `adjacentBlockEquiv_val` (`Langlands.Group.GL.AdjacentMergeShape`). They merge
  the blocks `j` and `j + 1` into one slot and refine it back.
- **Adjacent replacement.** `SegmentProductDatum.adjacentReplacementDatum`,
  `adjacentReplacementDatum_merged`, `adjacentReplacementDatum_of_ne`,
  `replaceAdjacentSlot`, `replaceAdjacentSlot_segments`,
  `replaceAdjacentSlot_hasSegmentSocles` and `replaceAdjacentSlotInducedEquiv`
  (`Langlands.Representation.Classification.SegmentProductSlotReplacement`).
- **Adjacent swap.** `SegmentProductDatum.adjacentSwappedDatum`,
  `adjacentSwappedDatum_merged_eq`, `adjacentSwappedDatum_of_ne` and
  `adjacentSwappedInducedEquiv`
  (`Langlands.Representation.Classification.SegmentProductAdjacentRefinement`).

## Implemented proof

1. **Two-layer embedding (`exists_injective_regroupedProduct_two_layers`).** This
   lemma is stated for an abstract regrouping `B, D, S, e, h, hc`, blocks `σ`,
   inner representations `τ`, equivalences `δ`, a slot `j`, and a length-two
   filtration `s` of `τ j` with positions `i ≠ i'`. Let `π` be irreducible with an
   injective `f` into the flat product. `exists_injective_graded`, applied to the
   regrouped slot filtration, gives a grade `k` and an injective map into its
   graded piece. Since `k : Fin 2` and `i ≠ i'`, `k = i` or `k = i'`. In the first
   case the map is composed with
   `regroupedProductSlotFiltrationGradedMap` for the outside equivalences `a` and
   the slot map `b`. In the second case it is composed with the map for `a'` and
   `b'`. Injectivity comes from `regroupedProductSlotFiltrationGradedMap_injective`.
   The lemma returns an injective map into `T.normalizedProductInduced D υ` or into
   `T.normalizedProductInduced D υ'`.
2. **Refinement case (`exists_injective_of_refinement_slot_two_layers`).** This is
   step 1 with `B = d.shape`, `σ = d.blocks`,
   `τ k = (d.refinementDatum D S e hs k).induced.representation`, and
   `δ = d.refinementDatumProductEquiv D S e hs`. The smoothness hypothesis on `τ`
   is `(d.refinementDatum D S e hs k).induced.isSmooth`.
3. **Merged pair (`LinkedReduction`).** `mergeShape`, `mergeRefinement`,
   `mergeLabel` and `mergeSlot` are the adjacent merge of `d.shape` at `j`.
   `fiber d j h k` is the refinement datum of slot `k`, and
   `pairDatum d j h = fiber d j h (mergeSlot d j h)`. The lemmas
   `pairDatum_length` (its length is `2`), `pairDatum_segments_zero` and
   `pairDatum_segments_one` show that its segments are `Δ'` and `Δ`, from
   `adjacentBlockEquiv_val`. `fiber_hasSegmentSocles` passes the socle property
   to every fiber. `pairReverse` is `pairDatum` permuted by its adjacent swap at
   `0`.
4. **Gluing (`linkedSegmentSocleEmbeddingReduction_of_gluing`).** The precedence
   `Δ'.Precedes Δ` is rewritten to the segments of `pairDatum`. The gluing
   hypothesis applied to `pairDatum` gives `U`, `I`, `e₂`, `s`, `i ≠ i'`, an
   equivalence `ε` from the piece at `i` to `e₂.induced`, and an injective `g` from
   the piece at `i'` into `pairReverse.induced`. The support conjunction is
   rewritten back to `Δ'` and `Δ`.
5. **Replacement products.** For the replaced branch, the outside equivalences
   `a` come from `adjacentReplacementDatum_of_ne` and the merged-slot
   equivalence `b` from `adjacentReplacementDatum_merged`, both through
   `inducedEquivOfBlockListEq`. For the swapped branch, `a'` comes from
   `adjacentSwappedDatum_of_ne` and `b'` from `adjacentSwappedDatum_merged_eq`, in
   the same way. Step 2 is applied with `b ∘ ε` at `i` and `b' ∘ g` at `i'`.
6. **Return.** If the embedding lands in the replacement outer product, it is
   composed with `replaceAdjacentSlotInducedEquiv`. This proves the second branch
   with `e = d.replaceAdjacentSlot j h e₂`, which has rank `n`. The list identity
   follows from `replaceAdjacentSlot_segments` and
   `List.ofFn e₂.segments = U :: I.toList`, by `simp`. The socle property is
   `replaceAdjacentSlot_hasSegmentSocles`. If the embedding lands in the swapped
   outer product, it is composed with `adjacentSwappedInducedEquiv.symm`, which
   proves the first branch.
7. **Final theorem.** `linkedSegmentSocleEmbeddingReduction F T` is
   `linkedSegmentSocleEmbeddingReduction_of_gluing F T (linkedSegmentSocleGluing F T)`.

## Dependency audit

The task excludes these items, with their conclusions, proof successors and
transitive proof dependencies:

- socle exhaustion f3a69bc8 (`MultisegmentSocleExhaustion`);
- segment analytic classification aca8805b
  (`SegmentEssentialSquareIntegrableClassification`);
- special-head multisegment exhaustion 3bfb61fa (`MultisegmentHeadExhaustion`);
- ordered special-head existence ebea9a8a (`OrderedMultisegmentHeadExistence`);
- quotient coverage 20e4e1c6 (`OrderedMultisegmentQuotientExhaustion`);
- tempered block uniqueness 52e97845 (`TemperedBlockUniqueness`);
- `SquareIntegrableLanglandsClassification` (task 1cb45da2);
- square-integrable exhaustion cd8ab97c (`SquareIntegrableLanglandsExhaustion`);
- regular exhaustion bf433f0a (`GLRegularLanglandsExhaustionStatement`).

The checks below were run against the module as submitted.

- **Import closure.** The module's project import closure has 1,386 modules.
  It contains no proof module of an excluded item, such as
  `MultisegmentSocleExhaustionProof`, `SegmentEssentialSquareIntegrableClassificationProof`,
  `MultisegmentHeadExhaustionProof`, `OrderedMultisegmentHeadExistenceProof`,
  `OrderedMultisegmentQuotientExhaustionProof`, `TemperedBlockUniquenessProof`,
  `SquareIntegrableLanglandsClassificationProof`,
  `SquareIntegrableLanglandsExhaustionProof` or `RegularLanglandsExhaustionProof`.
  The only closure modules whose names mention an excluded subject are
  `MultisegmentClassificationStatement`, `TemperedBlockStatement` and
  `RegularLanglandsStatement` (proposition definitions only), together with
  `OrderedMultisegmentHeadReduction` and `RegularLanglandsHeadReduction`.
  The last two are conditional assemblies that state their missing inputs as
  explicit hypotheses. A proposition definition or conditional assembly is not a
  proved input, and the constant traversal below shows that no excluded
  proposition is used. The sub-closures of the direct inputs are: the 4.6 proof
  used by the gluing proof, 1,374 modules; the two-factor Theorem 1.9 proof used
  by the gluing proof, 558 modules, with no `SegmentSocleCriterionHalves`,
  reverse-product or `ProductReversalFactors` module;
  `SegmentProductSlotReplacement`, 142 modules; and
  `RegroupedProductFiltration`, 147 modules.
- **Constant traversal.** A private diagnostic followed the types, values,
  constructors and recursors of all constants reachable from
  `linkedSegmentSocleEmbeddingReduction`. It found 95,442 constants, 16,397 of
  them from 1,146 project modules. None is an excluded proposition or a proof of
  one. A name search for exhaustion, socle or head existence, socle swap and
  commutation, embedding reduction, square-integrable Langlands, tempered block
  uniqueness, regular Langlands, essential square-integrable classification,
  `ProductReversalFactors` and `SegmentSocleProductIrreducibility` found only the
  following:
  - this module's declarations and the target statement;
  - the gluing proof and its inputs: Proposition 4.6
    (`linkedSegmentSocleReverseProductStructure` and its juxtaposed and
    quotient-map steps), two-factor Theorem 1.9
    (`twoFactorProductConstituentCommutativity`), and the sufficient
    irreducibility direction `unlinkedSegmentSocleProductIrreducible`, with their
    statement definitions;
  - `Geometric.finite_orbit_gluing`, a private lemma about orbit sections;
  - `RegularHeadExistence.nontrivial_normalizedProductInduction` from
    `RegularLanglandsHeadReduction`. It says that a normalized product of nonzero
    blocks is nonzero. In this closure it is used by
    `UnlinkedSegmentSocleProductIrreducibleProof` and
    `SegmentSocleJacquetReduction`. Its own dependencies are in the same
    traversal.

  The task allows the sufficient irreducibility direction to be reused.
- **Axioms.** `linkedSegmentSocleEmbeddingReduction` depends only on `propext`,
  `Classical.choice` and `Quot.sound`.

## Literature

Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
literature ID `zelevinsky-1980-induced-ii`, §6.7 (printed p. 190), the step
before Cases 1 and 2. The source argues that an irreducible submodule of the
product embeds into the product with the pair swapped or with the pair replaced
by `⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩`. It uses exactness and associativity of normalized
induction, Proposition 1.1(a),(c) (p. 170), and Proposition 4.6
(pp. 185–186) for the two factors. The Lean proof follows this route, as
described in the target statement's Markdown. The two-factor filtration of the
forward pair is the gluing input. Exactness and associativity are the regrouped
slot filtration and the ordered regrouping equivalence. The choice of layer is
`exists_injective_graded`.
