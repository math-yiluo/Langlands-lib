# Divisible uniform refinement indices

Author: Worker 167.

This internal supporting module identifies the finite minimal-permutation
indices whose specified standard source refinements have divisible piece sizes.
It completes the converse to the whole-target implication in
`UniformRefinementCombinatorics` and composes the resulting equivalence with
`TwoSourceShuffleLabels`. All declarations are in
`Langlands.Classification.ShuffleRefinement`.

For a field `K`, ordered shapes `B, C : BlockShape n`, a permutation `w`, and a
refinement `S : BlockRefinement B`, the general section retains the equality
`hS : sourceLevi K B C w = refinedLevi K B S`. The field universe is arbitrary.
Neither minimality nor divisibility is assumed in this section.

- `sourceBlockEmbedding_surjective_of_contained` assumes
  `TargetBlocksContained B C w`. For a piece `i` of source block `j`, it proves
  that the published `sourceBlockEmbedding B C w S hS j i` is surjective onto
  its containing target block.
- `source_size_eq_target_of_contained` compares finite cardinalities through
  the resulting bijection. The piece size equals the size of the target block
  containing the image of its first coordinate.

For surjectivity, take any coordinate `x` in that target block. Whole-target
containment places `w.symm x` in the original source block `j`. The source-block
coordinate equivalence expresses it as `B.index j a`. Its image under `w` is
`x`. The equality of target labels, together with
`SegmentEdge.sameBlock_of_sourceLevi_eq`, then places `a` in refinement piece
`i`. Decomposing `a` in that piece supplies its preimage. The size theorem uses
`Equiv.ofBijective`, `Nat.card_congr`, and the known cardinality of a block-index
fiber.

The uniform section fixes `hr : 0 < r`, a shape `B : BlockShape (m * r)`, and
the target `C = BlockShape.uniform m r hr`. With the same source-intersection
equality, `source_size_eq_of_contained` specializes the size theorem to
`(S j).size i = r`. Consequently
`source_divisible_iff_contained` proves the exact equivalence

```text
(∀ j i, r ∣ (S j).size i) ↔ TargetBlocksContained B C w.
```

The forward implication is the published `inverse_same_source_block`. The
reverse implication rewrites every piece size to `r`. These conclusions still
require no minimality hypothesis.

The family section takes an arbitrary supplied function
`S : MinimalRepresentatives B C → BlockRefinement B`. Its accompanying
hypothesis `hS` states the source-Levi equality for every representative.

- `DivisibleRefinementRepresentatives hr B S` is the subtype of the actual
  minimal representatives `w` satisfying `∀ j i, r ∣ (S w j).size i`.
  This type does not itself depend on `K` or `hS`.
- `divisibleEquivWholeTarget` uses `Equiv.subtypeEquivRight` and the proved
  equivalence of predicates. It changes the proof attached to a representative
  and preserves the actual permutation. `divisibleEquivWholeTarget_val`
  records preservation of the underlying minimal representative.
- `divisibleRefinementEquiv` compares two supplied refinement families, each
  satisfying its intersection equalities, by composing their equivalences
  through `WholeTargetRepresentatives`. This comparison also preserves the
  underlying permutation by construction.

For two source blocks, the parameters are natural numbers `m₀, m₁, r`, the
positive rank proof `hr`, an actual shape
`B : BlockShape ((m₀ + m₁) * r)`, a proof `h₂ : B.length = 2`, and the ordered
size equations
`B.size (Fin.cast h₂.symm 0) = m₀ * r` and
`B.size (Fin.cast h₂.symm 1) = m₁ * r`. The family `S` and all its
source-intersection equalities remain hypotheses.

- `divisibleEquivShuffles` composes `divisibleEquivWholeTarget` with the
  published `wholeTargetEquivShuffles`. Its codomain is exactly
  `{A : Finset (Fin (m₀ + m₁)) // A.card = m₀}`.
- `divisibleEquivShuffles_val` computes the forward subset: it consists of
  target blocks whose inverse images have source label zero, using the actual
  `targetBlockLabel` and the cast `Fin.cast h₂`.
- `divisibleEquivShuffles_symm_val` computes the inverse permutation as
  `permutationFromLabels hr B (assignmentFromSubset B h₂ h₀ h₁ A)`.
  Both formulas follow by unfolding the composed equivalences.
- `card_divisibleRefinementRepresentatives` transports cardinality through
  this equivalence and applies Mathlib's count of fixed-cardinality finite
  subsets. The result is
  `Nat.card (DivisibleRefinementRepresentatives hr B S) =
  (m₀ + m₁).choose m₀`.

The general and one-family results allow `m = 0`. In that case the positivity
and total-size conditions force the source shape to have no blocks. The
two-source hypotheses, with positive actual source-block sizes, force
`m₀ > 0` and `m₁ > 0`; no additional positivity assumptions are introduced.

The provenance is internal. The module uses finite coordinate equivalences,
the matrix-derived same-block criterion, finite cardinalities, and the
previously proved label parametrization. It cites no original literature.
The proved Library inputs used by the implementation and the reused
parametrization are:

| Input | Published location and originating task | Role and independence |
| --- | --- | --- |
| `sourceBlockEmbedding`, `inverse_same_source_block` | `Classification.UniformRefinementCombinatorics`, supporting unit of task `0c90f7e4-78fa-43fd-8736-238bb3e8617d` | Actual piece-coordinate embedding and the divisibility-to-containment direction, with the intersection equality retained. |
| `SegmentEdge.sameBlock_of_sourceLevi_eq` | `Classification.SegmentEdgeCombinatorics`, supporting unit of task `b331611c-526d-4925-87fe-ea67ed6e6fed` | Transposition matrices detect exactly when two coordinates belong to one refinement piece. The full segment Jacquet theorem is unused. |
| `exists_index_of_blockIndex_eq` | `Geometric.WeylUniquenessProof`, task `9ad51693-f8a1-45de-949a-72d07ecc13b9` | Decomposes a coordinate in a known block using the actual block coordinate equivalence. |
| `TotalConjugatingCount.card_blockIndex_fiber` | `CuspidalSupport.TotalConjugatingCountProof`, task `5becc159-1242-4fa4-9102-79aa6e2726c0` | Counts the coordinates in a block; no representation-theoretic result is used. |
| `wholeTargetEquivShuffles`, `assignmentFromSubset`, `permutationFromLabels` | `Classification.TwoSourceShuffleLabels` and `Classification.UniformTargetBlockLabels`, supporting units of task `0c90f7e4-78fa-43fd-8736-238bb3e8617d` | Actual finite labeling and increasing-coordinate permutation constructions. |
| `index_strictMono` | `Geometric.WeylMinimalRepresentativeProof`, task `6e35399b-9029-438e-9663-5ce96ab02576` | The reused label parametrization uses the prefix-sum order on block coordinates. |
| `blockIndex_index`, coordinate inverse laws, equivalence and finite-subset cardinality laws | Published `Geometric.WeylDefinitions`, `Group.GL.Blocks`, and Mathlib | Coordinate decomposition, bijection transport, and `Fintype.card_finset_len`. |

The recursive project import closure contains 80 modules, all unchanged from
the current Library. Its classification imports are exactly
`ConstituentRelations`, `SegmentEdgeCombinatorics`, `Segments`, `Supercuspidal`,
`SupercuspidalTwist`, `TwoSourceShuffleLabels`,
`UniformRefinementCombinatorics`, and `UniformTargetBlockLabels`. The remaining
imports provide lower matrix, block, field, twist, representation, and finite
Weyl infrastructure. There is no direct or transitive use of any excluded
classification, product irreducibility, commutation, gluing, exhaustion,
quotient-Hom, or derivative conclusion in the parent task's independence
conditions.

The divisibility predicate is only a finite predicate on supplied refinements.
This module does not assert that it characterizes nonzero geometric-lemma
pieces. It supplies neither a geometric-lemma filtration nor a Jacquet
representation formula. The full segment Jacquet formula, the shuffle Jacquet
formula, and the unconditional parent
`JuxtaposedSegmentSocleReverseProductStructure` remain separate proof
obligations.
