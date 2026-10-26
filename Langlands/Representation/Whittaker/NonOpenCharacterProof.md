# Radical character witnesses for non-open GL orbits

Lean proof: Worker 662. Mathematical specification and elementary-root route:
Worker 330, with the published statement and its convention checks by Worker 179.

The theorem `Langlands.Whittaker.nonOpenCharacterWitness` has complete type
`Langlands.Whittaker.NonOpenCharacterWitnessStatement`. It imports the existing
statement from `Langlands.Representation.Whittaker.NonOpenCharacterStatement`
without changing that pair or any imported definitions.

For every field `K` in an arbitrary universe, rank `n + 1`, ordered block shape
`B`, and raw additive character `ψ : AddChar K ℂ` with `ψ ≠ 1`, the theorem
constructs a witness for each actual minimal representative `v` satisfying
`v.val ≠ B.reversePermutation.symm`. The same element of the actual
`Geometric.orbitStabilizer` has identity Levi projection after applying
`Geometric.stabilizerToInducing` and nonidentity value under the ambient
`entrywiseCharacter`, as an element of `ℂˣ`.

## Recovering the excluded representative from antitone block labels

Read the original block labels along the ambient positions:

```text
f(x) = blockIndex B (v.symm x).
```

The helper `reverse_block_labels` computes the labels along
`B.reversePermutation`: they are the reversals of the labels of `B.reverse`.
The published `Geometric.blockIndex_monotone` therefore makes this sequence
antitone.

Suppose `f` is antitone as well. Mathlib's `Tuple.unique_antitone` says that
two antitone permutations of the same finite tuple agree. Applied to the tuple
`blockIndex B`, it identifies `f` with the labels along
`B.reversePermutation`. For each original block `i`, this equality gives
equality of the ranges of the two coordinate maps

```text
a ↦ v (B.index i a),
a ↦ B.reversePermutation.symm (B.index i a).
```

The first map is strictly increasing by the first clause of minimality.
The second is strictly increasing by
`B.reversePermutation_symm_index` and the published
`Geometric.index_strictMono` for the reversed shape. Mathlib's
`StrictMono.eq_of_range_eq` identifies the maps. The block-coordinate
equivalence covers every coordinate, proving that
`v = B.reversePermutation.symm`.

Consequently the excluded equality implies a strictly increasing adjacent
pair of inverse block labels. The helper `exists_adjacent_block_increase`
obtains `i : Fin n` with

```text
blockIndex B (v.symm i.castSucc) < blockIndex B (v.symm i.succ).
```

It uses `Fin.antitone_iff_succ_le` to pass from absence of such a pair to
the antitone case. This argument also covers rank one and one-block shapes:
when minimality forces the excluded representative, the inequality premise
has no instance. The singleton clause of minimality is not needed in this
argument; the input remains the original minimal-representative subtype.

## The matrix and its two properties

By `AddChar.ne_one_iff`, choose `t : K` with `ψ t ≠ 1`. At the adjacent pair
above, the helper `adjacentRoot` uses Mathlib's
`Matrix.GeneralLinearGroup.transvection` to form the actual invertible matrix

```text
u = 1 + t E_(i.castSucc,i.succ).
```

Mathlib supplies the inverse transvection with parameter `-t`. The proof
checks that all entries below the diagonal vanish and all diagonal entries
are one, making `u` an element of the original `upperUnipotent (n + 1) K`.

Put `w = GeneralLinear.permutation (n + 1) K v.val`.
The imported permutation-entry formulas give

```text
(w⁻¹ * u * w)(a,b) = u(v a,v b).
```

The sole added entry of this conjugate lies at the inverse images of the
chosen adjacent pair. Their original block labels strictly increase.
The helper `conjugate_root_identity_entry` thus shows that whenever
`blockIndex B b ≤ blockIndex B a`, the conjugate's `(a,b)` entry equals
the corresponding identity-matrix entry.

In particular all blocks strictly below the block diagonal vanish.
`B.mem_parabolic_iff` puts the conjugate in `B.parabolic K`, giving an
element `q` of the stated orbit stabilizer, whose convention is
`w⁻¹ * u * w ∈ B.parabolic K`. On each diagonal block the same entry formula
is exactly the identity. The imported
`B.mem_unipotentRadical_iff`, together with
`Geometric.stabilizerToInducing_apply`, therefore proves

```text
B.leviProjection K (Geometric.stabilizerToInducing _ _ w q) = 1.
```

Finally `adjacentRoot_sum` computes that the sum of the first-superdiagonal
entries of `u` is `t`. The existing `entrywiseCharacter_apply_sum` makes
the complex value of the ambient character exactly `ψ t`. If its value
in `ℂˣ` were one, coercion to `ℂ` would contradict the choice of `t`.
This proves character detection for the same `q`, with parameter `t`
and the original character sign.

## Imports, provenance, and scope

Besides the target's definitions, the proof imports the published
`WeylMinimalRepresentativeProof` for its block-coordinate order lemmas and
Mathlib's `LinearAlgebra.Matrix.ElementaryRowOperations` for invertible
transvections. Its tuple uniqueness, finite adjacency, equality of strictly
increasing maps with equal ranges, and matrix-entry arguments are internal
algebraic derivations from these imports.

The source motivation and precise Rodier manuscript citation are recorded in
[the unchanged statement documentation](NonOpenCharacterStatement.md).
The implemented proof follows the proposed GL elementary-root refinement
there, with finite tuple uniqueness supplying the combinatorial step.
It does not use a literature theorem as an additional hypothesis.
The arbitrary-field assertion is a derived refinement, rather than a literal
transcription of Rodier's p-adic formulation.

The distinguished permutation is the inverse block reversal, retaining the
coordinate order inside each block. The proof does not identify that
permutation with its inverse for unequal block sizes. It assumes no topology,
continuity, unitarity, representation, admissibility, or separately supplied
combinatorial witness. Its conclusion is the radical character witness;
induced-localization vanishing and Whittaker heredity require further results.
