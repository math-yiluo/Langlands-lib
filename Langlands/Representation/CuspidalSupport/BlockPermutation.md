# Reordering blocks and block maps of Levi-conjugating permutations

Authors: Worker 242, with two helper proofs from Worker 165.

This module provides the combinatorics needed to reduce statements about an
arbitrary Levi-conjugating permutation `w` between two standard block shapes to
statements about reorderings of blocks. It imports the published
`Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof` and
uses the existing `BlockShape`, `blockIndex`, `IsMinimalRepresentative`,
`ConjugatesLevi`, `blockWeyl` and `GeneralLinear.permutation` without changing
them.

## Provenance

All content is internal and derived. It is the standard description of the
Weyl-group elements `w` with `w M w⁻¹ = M'` for standard Levi subgroups of
`GL_n`: such a `w` permutes the diagonal blocks, and the minimal one in its
coset keeps the order of coordinates inside each block (compare
Bernstein–Zelevinsky 1977, §2, where these elements index the geometric
lemma). No new mathematical notion is introduced; `permute` and
`blockPermutation` are auxiliary constructions modelled on the published
`BlockShape.reverse` and `reversePermutation` of
`Langlands.Group.GL.ReverseBlocks`.

## Block reordering

For `B : BlockShape n` and `e : Equiv.Perm (Fin B.length)`, `B.permute e` has
the same number of blocks and size `B.size (e i)` at position `i`; positivity
is inherited and `Equiv.sum_comp` shows that the total rank is still `n`. So
block `i` of `B.permute e` is a copy of block `e i` of `B`. The sizes are
definitionally `B.size ∘ e`, and `(B.permute e).length = B.length`
definitionally, so `(B.permute e).permute s` is definitionally
`B.permute (e * s)`.

`B.permuteIndexEquiv e` is `Equiv.sigmaCongrLeft e`, sending the coordinate
`(i, x)` of the permuted shape to the coordinate `(e i, x)` of `B`.
`B.blockPermutation e : Equiv.Perm (Fin n)` composes it with the two standard
coordinate equivalences, so that

```
B.blockPermutation e (B.index (e i) x) = (B.permute e).index i x
```

(`blockPermutation_index`, and its inverse form
`blockPermutation_symm_index`). It moves block `e i` of `B` onto position `i`
and preserves the position inside the block. Consequently
`blockIndex_blockPermutation` gives
`blockIndex (B.permute e) (B.blockPermutation e a) = e.symm (blockIndex B a)`.

## Minimality on coordinates

`strictMono_index_iff` restates strict monotonicity of `w` on every block of
`B` as: whenever `a < b` lie in a common block of `B`, `w a < w b`. It uses the
published `index_strictMono` and `exists_index_of_blockIndex_eq`.
`isMinimalRepresentative_iff` applies this to both clauses of
`IsMinimalRepresentative B C w` (the clause for `w.symm` on blocks of `C`).

- `isMinimalRepresentative_blockPermutation`: `B.blockPermutation e` is a
  minimal representative from `B` to `B.permute e`, directly from the two
  index formulas.
- `isMinimalRepresentative_mul_inv`: if `w` is minimal from `B` to `C`, `u` is
  minimal from `B` to `B'`, and both `u` and `w` send coordinates to a common
  target block only when they come from a common source block, then `w * u⁻¹`
  is minimal from `B'` to `C`. The proof applies the coordinate form of the
  hypotheses at `u.symm a` and `w.symm c`.

## Levi conjugation through block maps

- `conjugatesLevi_of_blockIndex`: if a coordinate permutation `w` satisfies
  `(blockIndex C (w a) : ℕ) = f (blockIndex B a)` for an injective
  `f : Fin B.length → ℕ`, then `ConjugatesLevi B C w`. The block map is
  recorded through natural-number labels to avoid casts between `Fin`
  types of possibly different block counts. The proof characterizes Levi
  membership as vanishing of all entries between different blocks
  (`levi_mem_iff`, imported), and computes the entries of `P⁻¹ g P` for
  `P = permutation n F w` with the published `mul_permutation_entry`,
  `permutation_mul_entry` and `permutation_inv`: its `(a, b)` entry is
  `g (w a) (w b)`. Injectivity of `f` makes "different source blocks" and
  "different target blocks" equivalent.
- `conjugatesLevi_blockPermutation`: the canonical reordering conjugates the
  Levi of `B` onto that of `B.permute e`, with `f i = e.symm i`.
- `blockIndex_eq_of_conjugatesLevi`: a Levi-conjugating `w` keeps a common
  source block in a common target block. The transposition of two coordinates
  of one block of `B` lies in `blockWeyl B`, so the published
  `conjugatesLevi_weyl_mem` applies to it.
- `blockIndex_eq_of_conjugatesLevi_apply`: conversely, coordinates sent to a
  common target block come from a common source block (the previous result
  for `w⁻¹`, which conjugates the Levi of `C` back onto that of `B`).
- `exists_blockMap_of_conjugatesLevi`: every Levi-conjugating `w` induces a
  bijection of block labels. The map sends block `i` to the target block of
  the first coordinate of block `i`; it is well defined and injective by the
  two previous results and surjective by evaluating `w.symm` at the first
  coordinate of a target block. In particular `B.length = C.length`, and the
  result gives `e : Equiv.Perm (Fin B.length)` with
  `(blockIndex C (w a) : ℕ) = (e.symm (blockIndex B a) : ℕ)` for every
  coordinate `a`.

## Shared helpers

The theorems `levi_mem_iff` (membership in the embedded Levi is vanishing of
every entry between different blocks) and `conjugatesLevi_inv` (the inverse
permutation conjugates the target Levi back) are imported from
`MinimalConjugatingCosetsProof` by Worker 165. Their original proofs are now
public, so this module reuses them directly.
