# Uniform refinement shuffle realization

Author: Worker 167.

This internal supporting module packages actual target-block coordinates into a
block equivalence, proves conjugacy of the flattened source Levi with the uniform
target Levi, and evaluates the existing shuffle exponent at each source piece.
All declarations belong to `Langlands.Classification.ShuffleRefinement`.

## Block coordinates and conjugacy

Fix an arbitrary field `K`, natural numbers `m` and `r`, `hr : 0 < r`,
`B : BlockShape (m * r)`, an actual coordinate permutation `w`, and
`S : BlockRefinement B`. Write `C = BlockShape.uniform m r hr`. The source
intersection equality is an explicit hypothesis:

```text
hS : sourceLevi K B C w = refinedLevi K B S.
```

`refinementTargetIndex_sigma_surjective` proves that every target block is
`refinementTargetIndex hr B w S j i` for some nested source piece `(j,i)`.
Take coordinate zero in the target block, pull it back by `w`, and decompose it
first in `B` and then in `S j`. The source-piece embedding proves that its
target label is the requested one. Neither divisibility nor minimality is
needed for this surjectivity.

Suppose additionally `hdiv : ∀ j i, r ∣ (S j).size i`.
`refinementTargetIndex_sigma_injective` uses whole-target containment from
`inverse_same_source_block` to recover the outer source label from an equality
of target labels. The already proved injectivity within a fixed source block
then recovers its piece label. `refinementBlockEquiv` packages these two results
as an actual equivalence

```text
((j : Fin B.length) × Fin (S j).length) ≃ Fin m.
```

The definition depends on `hr`, `B`, `w`, `S`, `hS`, and `hdiv`; it requires no
minimality hypothesis. There is no restriction on the field universe or an
additional positivity assumption on `m`. At total rank zero all block index
types are empty.

`blockIndex_apply_flatten_index` uses the published `B.flatten_index` formula
to identify the target label of every coordinate in flattened block `k` with
`refinementTargetIndex` at `(B.flattenBlockEquiv S).symm k`. This lemma uses
`hS` alone.

`conjugatesLevi_flatten_uniform` proves the actual subgroup assertion

```text
ConjugatesLevi (F := K) (B.flatten S) C w.
```

The block-equivalence criterion `TotalConjugatingCount.conjugatesLevi_iff`
reduces this to equivalence of the source and image block-label equalities for
every pair of ambient coordinates. Decomposing the coordinates into flattened
blocks and applying `blockIndex_apply_flatten_index` reduces the claim to
injectivity of `refinementBlockEquiv`. This is equality of actual conjugate Levi
subgroups, not only a relation on their ranks. It uses divisibility but no
minimality.

## The actual two-source shuffle and its exponents

Now let the ambient rank be `(m₀ + m₁) * r`. The shape `B` has exactly two
source blocks, with explicit equations

```text
h₂ : B.length = 2,
h₀ : B.size (Fin.cast h₂.symm 0) = m₀ * r,
h₁ : B.size (Fin.cast h₂.symm 1) = m₁ * r.
```

Assume the same source intersection equality, divisibility of every refinement
size by `r`, and `hw : IsMinimalRepresentative B C w`. All these hypotheses are
retained. Positivity of the two source sizes, already part of `BlockShape`,
forces positive `m₀` and `m₁` under these size equations.

`refinementShuffle` applies the already constructed `wholeTargetEquivShuffles`
to the actual minimal permutation `w`, together with whole-target containment
from divisibility. It returns an actual finite subset of `Fin (m₀ + m₁)`
with cardinality `m₀`. It is the subset produced by that equivalence, with the
ordered first-source convention preserved.

`refinementShuffle_val` identifies this subset with
`sourceTargetBlocks hr B w (Fin.cast h₂.symm 0)`. Unfolding the equivalence
shows that membership is precisely a zero binary label; applying the inverse
finite cast recovers the original first-source label. The proof uses the
explicit classical decision instance used in `sourceTargetBlocks` when
applying finite-filter membership. `refinementShuffle_compl` identifies its
complement with the target blocks labeled by the second source block, since a
source label has exactly the two possible values.

The two final lemmas evaluate the published
`Langlands.Classification.shuffleExponent` at actual target indices. For the
first source they prove

```text
shuffleExponent (refinementShuffle ...).val a₀ a₁
  (refinementTargetIndex hr B w S (Fin.cast h₂.symm 0) i)
  = a₀ + (i.val : ℝ).
```

For the second source the same expression with source label `1` equals
`a₁ + (i.val : ℝ)`. The Lean names are
`shuffleExponent_refinementTargetIndex_zero` and
`shuffleExponent_refinementTargetIndex_one`.
The target-label lemma puts the index in the appropriate source-target set.
The subset or complement identity selects the corresponding branch of
`shuffleExponent`. Finally `card_sourceTargetBlocks_before` says that the
number of earlier target blocks with that source label is exactly `i.val`.
Thus these are evaluations of the existing exponent function, without a new
exponent convention or a representation-equivalence assumption.

## Provenance and dependency audit

The provenance is internal. The construction follows finite coordinate
surjectivity, injectivity, block-label comparison, and finite subset counting;
it cites no original literature as a mathematical input. Principal inputs are:

| Input | Module and originating task | Role and independence |
| --- | --- | --- |
| `inverse_same_source_block`, `sourceBlockEmbedding` | `UniformRefinementCombinatorics`, task `0c90f7e4-78fa-43fd-8736-238bb3e8617d` | Consequences of explicit source intersection equality and divisibility, proved by matrix and finite coordinate arguments. |
| `refinementTargetIndex_injective`, `refinementTargetIndex_label`, `card_sourceTargetBlocks_before` | `UniformRefinementCoordinates`, same parent task | Injectivity, actual source labels and the ordered earlier-position count; all stated hypotheses remain explicit. |
| `wholeTargetEquivShuffles` | `TwoSourceShuffleLabels`, same parent task | Actual equivalence from minimal permutations with whole-target containment to fixed-size subsets. |
| `targetBlockLabel`, whole-target label interfaces | `UniformTargetBlockLabels`, same parent task | Actual inverse coordinate labels and their finite cardinality constraints. |
| `B.flatten`, `B.flattenBlockEquiv`, `B.flatten_index` | `CuspidalSupport.MinimalJacquetProof`, task `f28607f5-1eef-4329-ae18-2576ef25ab6a` | Ordered flattening and its coordinate identity. The module's minimal-nonzero-Jacquet theorem is not invoked. Its lower refinement and coinvariant imports contain no excluded downstream classification input. |
| `TotalConjugatingCount.conjugatesLevi_iff` | `CuspidalSupport.TotalConjugatingCountProof`, task `5becc159-1242-4fa4-9102-79aa6e2726c0` | Actual Levi subgroup conjugacy is equivalent to preservation and reflection of block equality. Its proof is a permutation/transposition matrix argument over a field. |
| `blockIndex_index` | `Geometric.WeylDefinitions` | Finite coordinate inverse law. |
| `shuffleExponent` | `TwoSegmentSocleShuffleJacquetStatement`, statement arrangement task `efe00a4a-423f-449a-acf6-4e7e0eaf7f35` | Only the defined exponent function is used. The proposition `TwoSegmentSocleShuffleJacquet` is not assumed or proved. |

The separately submitted `UniformTargetBlockLabels`, `TwoSourceShuffleLabels`,
and `UniformRefinementCoordinates` pairs are integration prerequisites and must
be published before this module. The generic combinatorics pair is already a
Library input.

The recursive project import closure has 97 modules. Besides the above finite
support modules, its classification imports are `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`, `LanglandsData`,
`SegmentEdgeCombinatorics`, `Segments`, `Supercuspidal`, `SupercuspidalTwist`,
`Tempered`, and `TwoSegmentSocleShuffleJacquetStatement`. The additional
`Essential`, `Tempered`, and `LanglandsData` imports provide predicates, actual
data, and elementary transport facts; they do not provide any classification
existence or uniqueness result. The remaining imports are lower block, matrix,
refinement, induction, coinvariant, tensor, twist, filtration-definition,
coefficient-definition and representation infrastructure. The transitive closure
contains none of the parent's excluded reverse-product structure, reducibility,
socle or special-head product criterion, adjacent commutation, two-segment
commutation, linked gluing, ordered multisegment existence, exhaustion,
square-integrable classification, quotient-Hom, or derivative inputs.

The source intersection equality, divisibility, and the minimality needed for
the two-source shuffle remain hypotheses. No geometric-lemma filtration,
vanishing of other pieces, representation equivalence, segment Jacquet formula,
or shuffle Jacquet formula is proved here. This supporting unit does not prove
the unconditional parent `JuxtaposedSegmentSocleReverseProductStructure`.
