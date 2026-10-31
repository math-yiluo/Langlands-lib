# Two source-block labels as shuffle subsets

Author: Worker 167.

This internal supporting module specializes the finite labeling equivalence in
`UniformTargetBlockLabels` to a source shape with two blocks. All declarations
are in `Langlands.Classification.ShuffleRefinement`.

For a function `lab : Fin m → Fin 2`, `binarySubset lab` is the finite set of
indices with label zero. Conversely, `binaryLabel S` is zero on `S` and one on
its complement. The two constructions are inverse: a label in `Fin 2` that is
not zero is one. `card_binarySubset`, `card_binaryLabel_zero`, and
`card_binaryLabel_one` identify the two fiber cardinalities with the
cardinalities of `S` and its complement.

The two-source section fixes natural numbers `m₀`, `m₁`, and `r`, a proof
`hr : 0 < r`, and an actual ordered shape
`B : BlockShape ((m₀ + m₁) * r)`. Its hypotheses are
`h₂ : B.length = 2` and the size equalities
`B.size (Fin.cast h₂.symm 0) = m₀ * r` and
`B.size (Fin.cast h₂.symm 1) = m₁ * r`. The casts retain the actual ordered
source labels.

- `twoSourceBinaryLabel B h₂` transports a `LabelAssignment B` to a binary
  label function. `card_twoSourceBinaryLabel` transports each fiber along the
  inverse cast.
- `card_twoSource_zero` proves that its zero-labeled subset has cardinality
  `m₀`: the label assignment's size equation gives the equality after
  multiplication by `r`, and positivity permits cancellation.
- `assignmentFromSubset` builds a `LabelAssignment B` from any subset of
  `Fin (m₀ + m₁)` with cardinality `m₀`. Its first fiber has cardinality
  `m₀`; the complement formula gives cardinality `m₁` for the other fiber.
  The two supplied source-size equalities then prove both size constraints.
- `labelAssignmentEquivShuffles` packages these maps into an equivalence
  between `LabelAssignment B` and
  `{S : Finset (Fin (m₀ + m₁)) // S.card = m₀}`. The inverse laws use the
  binary inverse laws and the inverse finite casts.
- `wholeTargetEquivShuffles` composes this equivalence with
  `wholeTargetEquivLabels hr B`. Its domain is the actual
  `WholeTargetRepresentatives hr B`: minimal permutations from `B` to
  `BlockShape.uniform (m₀ + m₁) r hr` whose inverse sends each target block
  into a single source block.
- `card_wholeTargetRepresentatives` transports cardinality through this
  equivalence and applies Mathlib's `Fintype.card_finset_len`. The result is
  `Nat.card (WholeTargetRepresentatives hr B) = (m₀ + m₁).choose m₀`.

The provenance is internal. The implementation uses finite casts, the two
binary labels, multiplication cancellation, complement cardinalities, and the
standard count of fixed-cardinality subsets. It cites no original literature
and does not require a field, topology, or representation.

The companion finite-label module supplies `LabelAssignment`,
`WholeTargetRepresentatives`, and `wholeTargetEquivLabels`; its publication is
handled separately. Its coordinate proof depends on
`exists_index_of_blockIndex_eq` in `WeylUniquenessProof` (task
`9ad51693-f8a1-45de-949a-72d07ecc13b9`), `index_strictMono` in
`WeylMinimalRepresentativeProof` (task
`6e35399b-9029-438e-9663-5ce96ab02576`), and
`TotalConjugatingCount.card_blockIndex_fiber` in
`TotalConjugatingCountProof` (task
`5becc159-1242-4fa4-9102-79aa6e2726c0`). These are finite block-coordinate
results. The added Mathlib input is `Fintype.card_finset_len`; the other new
steps use finite set and cardinality laws.

The recursive project import closure has 70 modules, consisting of the
finite-label module and its 69 project imports. Its other classification
modules are `Segments`, `ConstituentRelations`, `Supercuspidal`, and
`SupercuspidalTwist`. The closure contains no excluded classification,
product irreducibility, commutation, gluing, exhaustion, quotient-Hom, or
derivative result. It invokes no geometric-lemma filtration or segment
Jacquet formula.

The whole-target condition remains part of the domain. The result counts
actual minimal permutations satisfying that condition; it does not identify
the nonzero geometric-lemma pieces, their representations, or any Jacquet
module. The shuffle Jacquet formula and the unconditional parent proposition
`JuxtaposedSegmentSocleReverseProductStructure` remain unproved by this module.
