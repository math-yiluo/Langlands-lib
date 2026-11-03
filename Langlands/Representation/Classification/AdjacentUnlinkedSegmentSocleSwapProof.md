# Adjacent unlinked segment-socle swaps in a full induced product

Author: Worker 769. The lifting module it uses was written with Worker 584.

`Langlands.Classification.adjacentUnlinkedSegmentSocleSwap` proves exactly
`Langlands.Classification.AdjacentUnlinkedSegmentSocleSwap.{uF,uV} F T` from
[AdjacentUnlinkedSegmentSocleSwapStatement](AdjacentUnlinkedSegmentSocleSwapStatement.md).
Its outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`. The field universe `uF` and the carrier universe `uV`
are independent. The theorem has no further hypotheses, and in particular no
theorem-valued ones. Inspection reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The conclusion is an actual isomorphism in the category of smooth complex
representations of `GL_n(F)`:
`Nonempty (d.induced ≅ (d.permute (d.shape.adjacentSwap j h)).induced)`. It is
not a statement about composition factors, and the full product may be
reducible. The supplied topology, the standard upper block parabolic, the
normalized induction with positive half-modulus covariance, and right
translation are the ones in the published definitions. None of them is changed.

## Implemented proof

After installing `T.topology`, fix a rank `n`, an actual datum
`d : T.SegmentProductDatum.{max uF uV, uF} n` with socle witnesses
`hd : d.HasSegmentSocles`, an index `j` with `h : j + 1 < d.length`, and the
hypothesis `hu` that the segments at positions `j` and `j + 1` are not linked.
No condition is placed on the other segments: they may be linked, repeated or
equal. The argument is uniform in the rank and makes no case split. At rank zero
no index `j` satisfies `h`, so that case is vacuous.

1. **Lifting.** The published theorem
   `Langlands.Classification.AdjacentSegmentSwapLifting.lift d j h` reduces the
   goal to a single isomorphism between the two orders of the merged two-block
   datum `a := AdjacentSegmentSwapLifting.mergedFiber d j h`:
   `Nonempty (a.induced ≅ (a.permute (a.shape.adjacentSwap 0 _)).induced)`.
   This lifting step is the regroup, replace and ungroup route over the common
   outer shape `d.shape.adjacentMerge j h`. It applies
   `Langlands.Parabolic.orderedProductRegrouping` to the direct adjacent
   refinement (`regroup_direct`) and to the swapped one (`regroup_swapped`).
   Both regroupings use the actual blocks and the published coordinate identities
   `adjacent_index` and `adjacentSwap_index`. At the merged slot, the
   two-block isomorphism is inserted after identifying the swapped fiber with
   `a.permute (a.shape.adjacentSwap 0 _)` (`swappedFiber_eq_permute`). At every
   other slot, the direct and swapped single-block inner data are equal
   (`swappedFiber_eq_of_ne`), and the identity is used. The family is mapped
   through `T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)` by
   `Pi.isoMk`. The direct regrouping, this mapped family and the inverse swapped
   regrouping are then composed. The endpoint is the literal
   `(d.permute (d.shape.adjacentSwap j h)).induced`. Inner rank equalities hold
   by definition, so rank transports are `eqToIso` of definitional
   unfoldings. The lifting module's Markdown,
   [AdjacentSegmentSwapLifting](AdjacentSegmentSwapLifting.md), describes these
   steps in detail.

2. **Hypotheses for the merged datum.** `mergedFiber_length` gives
   `a.length = 2`. The segments of `a` at positions `0` and `1` are rewritten
   by `mergedFiber_segments_zero` and `mergedFiber_segments_one` to
   `d.segments ⟨j, _⟩` and `d.segments ⟨j + 1, h⟩`, so `hu` becomes the
   nonlinkage hypothesis for `a`. The socle witnesses of `a` are
   `directFiber_socles d j h hd` at the merged outer block. They evaluate `hd`
   at the original labels `j` and `j + 1`, so they refer to the supplied blocks
   themselves.

3. **The two-factor isomorphism.** The published theorem
   `Langlands.Classification.twoSegmentSocleCommutation.{uF, uV} F T`, applied
   to the rank of `a`, the datum `a`, `a.length = 2`, these socle witnesses and
   the nonlinkage hypothesis, gives exactly the isomorphism required in step 1.
   Its datum lives in the same universe `max uF uV` as `d`.

The permuted datum keeps every supplied block with its segment and sends a new
position `i` to the old label `(d.shape.adjacentSwap j h) i`, as in the
published `SegmentProductDatum.permute`.

## Provenance

The target is the actual-product form of Zelevinsky 1980, Proposition 6.4(1),
printed p.189 (registered source `zelevinsky-1980-induced-ii`). The statement
Markdown records the source correspondence, which is unchanged here, and the
ingredients of the printed proof. Those ingredients are associativity and
commutativity (§§1.7, 1.9) and the irreducibility criterion of Theorem 4.2. The
Lean proof separates the two-factor case, proved in
`TwoSegmentSocleCommutationProof`. It then inserts that actual isomorphism into
the full product by induction in stages and functoriality of the outer
normalized product. No step here infers an isomorphism from composition-factor
equality alone.

## Dependency audit

The direct imports are:

- `Classification.AdjacentUnlinkedSegmentSocleSwapStatement`, the unchanged
  target statement;
- `Classification.TwoSegmentSocleCommutationProof`, the accepted proof of
  `TwoSegmentSocleCommutation` from task 66e3b87c-647e-41e4-af18-df4d436765f0
  (lean.proof `7db3cad5-2050-4607-bce8-6df4f8a68206`). Its Markdown records
  its own dependency audit. The proof uses the published
  `unlinkedSegmentSocleProductIrreducible` and
  `twoFactorProductConstituentCommutativity`, together with a generic
  Jordan–Hölder bridge between irreducible representations with the same
  factors;
- `Classification.AdjacentSegmentSwapLifting`, the accepted generic lifting
  construction (lean.definition `119b1c0f-6a96-499d-852f-8de042228a3b`). It
  imports only `Classification.SegmentProductPermutation` and
  `Parabolic.OrderedProductRegroupingProof`. It assumes no head, socle, linkage,
  irreducibility or commutation result.

Both theorem inputs were accepted and published before this proof used them.
Neither takes a theorem-valued hypothesis. The two-factor input is not
obtained from the present full-product conclusion or its two-block
specialization. The import closure of `TwoSegmentSocleCommutationProof` has
1,315 `Langlands` modules. It contains neither this module, its statement nor
the lifting module.

The audit used the workspace over Library commit
`83afd4553e9b793a825b53a9504028c880852999`.

- **Imports.** Following imports recursively from this module reaches 1,318
  `Langlands` modules, and no project import is missing. None of the following
  proof modules is in this closure:
  - the excluded proof modules `MultisegmentSocleExhaustionProof`,
    `SegmentEssentialSquareIntegrableClassificationProof`,
    `MultisegmentHeadExhaustionProof`, `OrderedMultisegmentHeadExistenceProof`,
    `OrderedMultisegmentQuotientExhaustionProof`,
    `TemperedBlockUniquenessProof`,
    `SquareIntegrableLanglandsClassificationProof`,
    `SquareIntegrableLanglandsExhaustionProof`,
    `RegularLanglandsExhaustionProof` and
    `OrderedMultisegmentSocleExistenceProof`;
  - any module of the special-head `AdjacentUnlinkedSegmentSwap` or
    `TwoSegmentHeadCommutation`.
- **Constants.** A private Lean diagnostic traversed every constant reachable
  from `adjacentUnlinkedSegmentSocleSwap`. It followed types, values (including
  opaque ones), constructors, inductive families and recursors. It reached
  94,320 constants, of which 15,364 are project constants defined in 1,077
  project modules. No reachable constant or defining module has a name
  containing any of:
  - the excluded conclusions `MultisegmentSocleExhaustion`,
    `SegmentEssentialSquareIntegrableClassification`,
    `MultisegmentHeadExhaustion`, `OrderedMultisegmentHeadExistence`,
    `OrderedMultisegmentQuotientExhaustion`, `TemperedBlockUniqueness`,
    `SquareIntegrableLanglandsClassification`,
    `SquareIntegrableLanglandsExhaustion`, `RegularLanglandsExhaustion` or
    `OrderedMultisegmentSocleExistence`;
  - `AdjacentUnlinkedSegmentSwap` or `TwoSegmentHeadCommutation`;
  - the substring `Exhaustion`.

  The check was case-insensitive, so it also covered the lowercase theorem
  names.

Imported statement modules define several excluded propositions, for example
in `MultisegmentClassificationStatement`, `TemperedBlockStatement` and
`RegularLanglandsStatement`. They also contain conditional assemblies such as
`orderedMultisegmentHeadExistence_of_prerequisites` in
`OrderedMultisegmentHeadReduction`. These definitions and conditional theorems
are imported but do not supply their conclusions. The constant traversal shows
that the proof does not reach them. The only constants of
`RegularLanglandsHeadReduction` that are reached are generic. One example is
the nonzero-product lemma `RegularHeadExistence.nontrivial_normalizedProductInduction`,
which the irreducibility input uses.

Hence the proof is independent, directly and transitively, of the conclusions,
proof successors and proof dependencies of the excluded tasks. These are
independent socle exhaustion (f3a69bc8), segment analytic classification
(aca8805b), special-head multisegment exhaustion (3bfb61fa), ordered
special-head existence (ebea9a8a), quotient coverage (20e4e1c6), tempered block
uniqueness (52e97845), `SquareIntegrableLanglandsClassification` (1cb45da2),
square-integrable exhaustion (cd8ab97c), regular exhaustion (bf433f0a) and
`OrderedMultisegmentSocleExistence` (23189526).
