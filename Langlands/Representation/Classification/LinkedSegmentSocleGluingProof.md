# Proof of the gluing of the forward product of two linked segment socles

Author: Worker 773.

This module proves
`Langlands.Classification.linkedSegmentSocleGluing :
LinkedSegmentSocleGluing.{uF,uV} F T`, with outer arguments
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`. The
universes `uF`, `uV` stay independent and the prime is arbitrary. The proof
combines the published proofs of Zelevinsky's Proposition 4.6 for the reverse
product and of the two-factor case of Ze80 Theorem 1.9 with the Library
Jordan–Hölder comparison. It also states two conditional forms:
`linkedSegmentSocleGluing_of` takes both propositions as hypotheses, and
`linkedSegmentSocleGluing_of_reverseProductStructure` takes only 4.6. The final
theorem applies them to the published proofs. It has no extra hypotheses.

## Target

`Langlands.Classification.LinkedSegmentSocleGluing.{uF,uV} F T` from
`Langlands.Representation.Classification.LinkedSegmentSocleGluingStatement`
(statement candidate c84cd52c-3ff3-4024-be50-8b84dd480888). Take a datum
`d : T.SegmentProductDatum.{max uF uV, uF} n` of length two with segment socle
blocks `⟨Δ'⟩, ⟨Δ⟩`, where `Δ' = d.segments 0` precedes `Δ = d.segments 1`. The
statement asks for:

- the union `U` and the optional intersection `I`, with
  `Δ'.IsUnionIntersectionReplacement Δ U I`;
- a segment-socle datum `e` at rank `n` with `List.ofFn e.segments = U :: I.toList`;
- a two-step filtration `s` of the forward product `⟨Δ'⟩ × ⟨Δ⟩ = d.induced`, with
  two distinct positions `i ≠ j`. The graded piece at `i` is equivalent to
  `e.induced = ⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩`. The graded piece at `j` embeds injectively
  into the reverse product `⟨Δ⟩ × ⟨Δ'⟩ = (d.permute σ).induced`, where
  `σ = d.shape.adjacentSwap 0 _` is the adjacent swap.

## Inputs

- Ze80 Proposition 4.6:
  `Langlands.Classification.linkedSegmentSocleReverseProductStructure`
  (module `LinkedSegmentSocleReverseProductStructureProof`, lean.proof
  37c0363b-6771-4aca-bd32-e00cc4d81ee1, task a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9,
  Worker 219). It proves the statement `LinkedSegmentSocleReverseProductStructure`
  from `SegmentSocleCriterionHalvesStatement` (candidate
  05b27752-ea74-478e-b16d-43a92a59833b). It is used at universes
  `uF, max uF uV`.
- Ze80 Theorem 1.9, two-factor case:
  `Langlands.Classification.twoFactorProductConstituentCommutativity`
  (module `TwoFactorProductConstituentCommutativityProof`, lean.proof
  016ebb10-d2e9-4e71-8948-3f051e6fafb9, task afd5ae37-9c4e-44fe-897a-623bb2c92d91).
  It proves the statement `TwoFactorProductConstituentCommutativity` (candidate
  32426f28-fdb1-44b3-8f12-bc80de4ffc1c). It is used at universes `uF, max uF uV`.
- Library: `jordanHolderSeriesComparison`
  (`Filtration/JordanHolderComparisonProof`), `LengthCriterionProof.quotientRep`
  and `lower`, `ObjectRepFiltration` and `HaveSameJordanHolderFactors`
  (`Filtration/ObjectDefinitions`), and `SegmentProductDatum.permute` with
  `permute_induced`.

Both proofs are accepted and public at Library commit
25b91125ea94e88d741b206d633e82eb0d87c3e5.

## Implemented proof

1. **Reverse product (Ze80 4.6).** The swap values `σ 0 = 1` and `σ 1 = 0` come
   from `Equiv.swap_apply_left` and `Equiv.swap_apply_right`. So `d.permute σ`
   has segments `Δ, Δ'`, its blocks are segment socles, and its segment 1 (`Δ'`)
   precedes its segment 0 (`Δ`). Proposition 4.6, applied to `d.permute σ`,
   gives `U`, `I`, `e` and a filtration `s'` of the reverse product
   `(d.permute σ).induced`. `s'` has simple factors, and its top graded piece
   `s'.graded 1` is equivalent to `e.induced`. The proof does not use the
   irreducibility of `e.induced`, the non-isomorphism clause or the uniqueness
   clause.
2. **Order of the replacement.** 4.6 returns
   `Δ.IsUnionIntersectionReplacement Δ' U I`, after rewriting the segments of
   `d.permute σ` with the swap values. The target needs
   `Δ'.IsUnionIntersectionReplacement Δ U I`. The lemma
   `Segment.IsUnionIntersectionReplacement.comm`, proved here, gives this from
   commutativity of set union and intersection. The data `e`,
   `List.ofFn e.segments = U :: I.toList` and `e.HasSegmentSocles` are passed
   on unchanged.
3. **Same composition factors (Ze80 1.9).** Every block of `d` is irreducible:
   this is the first conjunct of `IsIrreducibleSocle`, from `IsSegmentSocle`.
   The 1.9 statement is applied with `B = d.shape` and `A = d.blocks`. Since
   `permute_induced` holds by `rfl`, it gives
   `HaveSameJordanHolderFactors (Rep.of d.induced.representation)
   (Rep.of (d.permute σ).induced.representation)`.
4. **Length-two transfer (`exists_lengthTwo_transfer`).** This is an abstract
   lemma for representations `ρ`, `σ` of a monoid over a field. Same
   Jordan–Hölder factors give a composition series `s` of `ρ`, a composition
   series `t` of `σ` and a matching of their graded pieces. The series `t` is
   compared with the given length-two series `u` of `σ` by
   `jordanHolderSeriesComparison`. The resulting bijection
   `Fin n ≃ Fin 2` forces `n = 2` (`Fintype.card_congr`). Composing the two
   matchings, `φ = e.trans g`, gives positions `i = φ⁻¹ 1` and `j = φ⁻¹ 0` of
   `s`, with `s.graded i ≃ u.graded 1` and `s.graded j ≃ u.graded 0`. They
   are distinct because `φ⁻¹` is injective.
5. **Bottom piece embeds (`exists_injective_gradedRepresentation_zero`).**
   `u.graded 0` is the successive quotient of `u.sub 1` by `u.sub 0 = ⊥`
   (`exists_injective_quotientRep_of_eq_bot`). The inclusion of `u.sub 1`
   vanishes on `lower ⊥ (u.sub 1)`, so it lifts to the quotient
   (`Submodule.liftQ`). The lift intertwines the actions, and it is injective
   because its kernel is `⊥` (`Submodule.ker_liftQ_eq_bot`).
6. **Assembly.** Step 4 is applied to `ρ = d.induced`, `σ = (d.permute σ).induced`
   and `u = s'`. The piece of `s` at `i` is equivalent to `e.induced`, by
   composing `s.graded i ≃ s'.graded 1` with the 4.6 equivalence. The piece at
   `j` maps into the reverse product by the composite of
   `s.graded j ≃ s'.graded 0` with the embedding of step 5. This composite is
   injective.

## Dependency audit

The task excludes the following, with their conclusions, proof successors and
transitive proof dependencies:

- linked full-product reduction 0f459af5 and `LinkedSegmentSocleEmbeddingReduction`;
- socle exhaustion f3a69bc8 (`MultisegmentSocleExhaustion`);
- ordered socle existence 23189526 (`OrderedMultisegmentSocleExistence`);
- adjacent unlinked socle swap e3634665 (`AdjacentUnlinkedSegmentSocleSwap`);
- two-segment socle commutation 426911b4 (`TwoSegmentSocleCommutation`);
- segment analytic classification aca8805b
  (`SegmentEssentialSquareIntegrableClassification`);
- multisegment special-head exhaustion 3bfb61fa (`MultisegmentHeadExhaustion`);
- ordered special-head existence ebea9a8a (`OrderedMultisegmentHeadExistence`);
- quotient coverage 20e4e1c6 (`OrderedMultisegmentQuotientExhaustion`);
- tempered block uniqueness 52e97845 (`TemperedBlockUniqueness`);
- `SquareIntegrableLanglandsClassification` (1cb45da2);
- square-integrable exhaustion cd8ab97c (`SquareIntegrableLanglandsExhaustion`);
- regular exhaustion bf433f0a (`GLRegularLanglandsExhaustionStatement`).

Checks:

- **Import closure.** The module's project import closure has 1,378 modules. It
  contains none of the corresponding proof modules, such as
  `MultisegmentSocleExhaustionProof`, `OrderedMultisegmentSocleExistenceProof`,
  `MultisegmentHeadExhaustionProof`, `OrderedMultisegmentHeadExistenceProof`,
  `OrderedMultisegmentQuotientExhaustionProof`, `TemperedBlockUniquenessProof`,
  `SquareIntegrableLanglandsClassificationProof`,
  `SquareIntegrableLanglandsExhaustionProof`, `RegularLanglandsExhaustionProof`
  or `SegmentEssentialSquareIntegrableClassificationProof`. It also contains no
  module for `LinkedSegmentSocleEmbeddingReduction`, `AdjacentUnlinkedSegmentSocleSwap`
  or `TwoSegmentSocleCommutation`. Some imported statement modules define
  excluded propositions (`MultisegmentClassificationStatement`,
  `TemperedBlockStatement`, `RegularLanglandsStatement`). A proposition
  definition is not a proved input, and the constant traversal below shows that
  none of them is used.
- **Constant traversal.** A private diagnostic followed the types, values,
  constructors and recursors of all constants reachable from
  `linkedSegmentSocleGluing`. It found 95,266 constants, 16,251 of them from
  1,136 project modules. No excluded proposition or theorem occurs among them.
  A name search for exhaustion, socle existence, head existence, socle swap,
  socle commutation, embedding reduction, square-integrable Langlands, tempered
  block uniqueness, regular Langlands and gluing found only unrelated or local
  constants. These are this module's own declarations and the target statement,
  Library rank-zero lemmas, `Geometric.finite_orbit_gluing`, and the helper
  `RegularHeadExistence.nontrivial_normalizedProductInduction`. That helper is a
  shared lower-level lemma (a normalized product induction is nonzero) from
  `RegularLanglandsHeadReduction`, and its own dependencies are in the same
  traversal.
- **Axioms.** `linkedSegmentSocleGluing` depends only on `propext`,
  `Classical.choice` and `Quot.sound`.

## Literature

Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
literature ID `zelevinsky-1980-induced-ii`: Proposition 4.6 (pp. 185–186),
Theorem 1.9 (p. 174), and the gluing sentence of §6.7 (p. 190). The Lean proof
follows the route of the target statement's Markdown. Proposition 4.6 is about
the reverse product `⟨Δ⟩ × ⟨Δ'⟩`. The filtration of the forward product here is
obtained only from its Jordan–Hölder factors, through 1.9 and the comparison of
composition series.
