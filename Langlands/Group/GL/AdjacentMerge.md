# Actual groups for adjacent merged blocks

Author: Worker 328. Worker 379 supplied the concrete coordinate interface in
`AdjacentMergeShape` and its specialization argument lists.

This module joins the published finite constructions in
[AdjacentMergeShape](AdjacentMergeShape.md) to the actual group comparisons in
[RefinementCoordinates](RefinementCoordinates.md). All new declarations are in
`Langlands.GeneralLinear.BlockShape` and have explicit prefix `B j h R`, where
`B : BlockShape n`, `j : ℕ`, `h : j + 1 < B.length`, and `R : Type u` is a
commutative ring. The continuous versions also assume `TopologicalSpace R` and
`IsTopologicalRing R`. No coordinate identity or subgroup comparison is an
additional input.

## Shapes and coordinates reused

Write `D = B.adjacentMerge j h`, `S = B.adjacentRefinement j h`,
`C = B.permute (B.adjacentSwap j h)`, and
`T = B.adjacentSwapRefinement j h`. These are imported constructions, not new
parameters. The merge has length `B.length - 1`, retains earlier sizes, adds
the original sizes at `j` and `j + 1`, and shifts later labels once. The merged
component of `S` has those two original sizes in order; every other component
has one block. `adjacentCollapse` sends an original block label `b` to `b` for
`b ≤ j` and to `b - 1` otherwise. `blockIndex_adjacentMerge` and
`adjacentMerge_indexEquiv_symm_fst` give its actual coordinate compatibility.

The imported `adjacentSwap` is the transposition
`Equiv.swap ⟨j, _⟩ ⟨j + 1, h⟩` on `Fin B.length`.
`adjacentMerge_permute_adjacentSwap` proves `C.adjacentMerge j h = D`.
The refinement `T` already lies over this same `D`, with the size casts built
into its construction. `adjacentSwapRefinement_size_merged_rev` reverses the
two inner sizes, and `adjacentSwapRefinement_of_ne` proves equality of the
one-block components elsewhere. Thus both group constructions below use
literally the same outer shape, without requiring the user to transport it.

## Group interface

In the following table, the two columns give the original and swapped names.
Every name takes the prefix `B j h R`; the original source shape is `B` and
refinement is `S`, while the swapped source shape is `C` and refinement is `T`.

| Original declaration | Swapped declaration | Meaning |
| --- | --- | --- |
| `adjacentLeviEquiv` | `adjacentSwapLeviEquiv` | Multiplicative equivalence from the source Levi to `Geometric.refinedLevi R D` of the indicated refinement. |
| `adjacentLeviEquiv_val` | `adjacentSwapLeviEquiv_val` | Each outer component is the actual inner block-diagonal embedding of the reindexed source blocks. |
| `adjacentLeviEquiv_entry` | `adjacentSwapLeviEquiv_entry` | Applying `refinedLeviEquiv.symm` and reading inner entry `(i,k,x,y)` gives source block `e ⟨i,k⟩` at the two `Fin.cast hs` coordinates. |
| `adjacentLeviEmbedding` | `adjacentSwapLeviEmbedding` | Applying `D.leviEmbedding` to the resulting refined Levi gives exactly the source shape's ambient Levi embedding. |
| `adjacentComposedParabolic_eq` | `adjacentSwapComposedParabolic_eq` | Equality of `Parabolic.composedParabolic R D` of the indicated refinement with the source shape's actual parabolic subgroup. |
| `adjacentParabolicEquiv` | `adjacentSwapParabolicEquiv` | Multiplicative equivalence from the source parabolic to that composed parabolic. |
| `adjacentParabolicEquiv_val` | `adjacentSwapParabolicEquiv_val` | The parabolic equivalence retains the underlying ambient matrix. |
| `adjacentComposedLeviProjection` | `adjacentSwapComposedLeviProjection` | Composed projection after the parabolic equivalence equals source projection followed by the Levi equivalence. |
| `adjacentLeviEquivContinuous` | `adjacentSwapLeviEquivContinuous` | The same Levi equivalence, continuous in both directions. |
| `adjacentParabolicEquivContinuous` | `adjacentSwapParabolicEquivContinuous` | The same parabolic equivalence, continuous in both directions. |

For each continuous equivalence, the theorem with suffix `_toMulEquiv`
identifies its underlying multiplicative equivalence with the corresponding
noncontinuous name. The `_val`, `_entry`, and `_toMulEquiv` laws are simp lemmas.

For clarity, the direct embedding and projection laws say precisely

```text
D.leviEmbedding R (B.adjacentLeviEquiv j h R m).val = B.leviEmbedding R m

Parabolic.composedLeviProjection R D S (B.adjacentParabolicEquiv j h R g)
  = B.adjacentLeviEquiv j h R (B.leviProjection R g).
```

The swapped laws replace the source `B` by `C`, use refinement `T`, and use
the names beginning `adjacentSwap`. They preserve the ambient matrix for `C`;
they do not identify the ambient matrices of `B` and `C` with one another.

## Implemented construction and proofs

For the original shape, apply the generic constructors with
`B D S (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R`.
The actual ambient embedding, parabolic equality and projection comparison
then follow by supplying the proved coordinate identity `B.adjacent_index j h`.
For the swapped shape, use
`C D T (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R`
and the proved identity `B.adjacentSwap_index j h`.

These are direct specializations of the published constructions. In particular,
the Levi equivalence reindexes the source blocks, casts their matrix sizes and
then applies the existing `Geometric.refinedLeviEquiv`. The outer-component
formulas are definitional. The entry formulas cancel `refinedLeviEquiv` with
its inverse and reduce to the nested product's matrix entry. The ambient,
subgroup and projection proofs apply the corresponding generic theorems with
the concrete coordinate identities. The continuous constructors reuse the
generic continuous versions, and the `_toMulEquiv` equalities are definitional.

## Provenance and scope

This is derived internal geometry over the imported `BlockShape`,
`Geometric.BlockRefinement`, `Geometric.refinedLeviEquiv`,
`Parabolic.composedParabolic` and actual diagonal projections. The two imported
modules supply all finite coordinates and the general group comparison proofs.
This module specializes their data and exposes a concrete adjacent-block API.

The motivation is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), §2.16(2) and Lemma 2.17, printed page 450,
PDF page 11 (zero-based index 10). This passage describes elementary maps for
`GL(n,F)` by transposing neighbouring blocks within a larger standard subgroup.
The arbitrary-commutative-ring constructions here are internal deductions,
not a theorem transcribed from that passage. The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
registered as `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
No source-specific errata file was present at preparation.

The module establishes only the adjacent-merge group and coordinate geometry.
It contains no normalization, modulus, induced representation equivalence,
factor matching or association theorem.
