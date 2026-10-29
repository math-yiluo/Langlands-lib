# Block coordinates on the lower triangular group

Author: Worker 936.

This module identifies the group `B̄_{a+d}` of invertible lower triangular
`(a+d) × (a+d)` matrices with the product

```text
B̄_a × M_{d×a} × B̄_d ,   (b, x, h) ↦ [[b, 0], [x, h]] ,
```

and writes the group law of `B̄_{a+d}` in these coordinates:

```text
(b, x, h) · (b', x', h') = (b b', x b' + h x', h h').
```

The equivalence holds for every commutative ring `R`. It is a homeomorphism
for every topological commutative ring. All declarations are in the
namespace `Langlands.GeneralLinear`.

## Provenance

Internal (derived infrastructure). In H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983),
section 9.3, the measure on the lower-block coordinates `([g], x, h)` of
`N_{a+d} \ GL_{a+d}` is written `dg d_r(h) dx`. This module is used to compare
that product measure with a right Haar measure on `B̄_{a+d}`. The source
states no lemma of this form. The facts proved here are elementary block
matrix algebra, proved from the Library definitions named below.

## Conventions

- `lowerTriangularSubgroup n R` is the published subgroup of
  `GeneralLinear n R` whose matrices are lower triangular
  (`mem_lowerTriangularSubgroup_iff`: `g i j = 0` whenever `i < j`).
- `lowerBlockPair g x h` is the published matrix `[[g, 0], [x, h]]` in
  `GeneralLinear (a + d) R`, for `g : GeneralLinear a R`,
  `x : Matrix (Fin d) (Fin a) R` and `h : lowerTriangularSubgroup d R`. Its
  blocks are read off by `lowerBlockPair_11`, `_12`, `_21`, `_22` on the
  indices `Fin.castAdd d` (first `a` indices) and `Fin.natAdd a` (last `d`
  indices).
- Topologies: `GeneralLinear n R` carries the units topology, subgroups the
  subspace topology, and `Matrix (Fin d) (Fin a) R` the product topology.
  These are the Library and Mathlib instances. No new instance is installed.

## Definitions

- `lowerTriangularFirstBlock k : lowerTriangularSubgroup a R`, for
  `k : lowerTriangularSubgroup (a + d) R`: the upper left `a × a` block of
  `k`. Its inverse is the upper left block of `k⁻¹`. Both inverse identities
  come from the product formula `lowerTriangular_mul_apply_castAdd` below.
  Simp lemma `lowerTriangularFirstBlock_apply`.
- `lowerTriangularLastBlock k : lowerTriangularSubgroup d R`: the lower right
  `d × d` block of `k`, with inverse the lower right block of `k⁻¹`
  (via `mul_lowerTriangular_apply_natAdd`). Simp lemma
  `lowerTriangularLastBlock_apply`.
- `lowerTriangularRectangle k : Matrix (Fin d) (Fin a) R`: the lower left
  `d × a` block of `k`.
- `lowerTriangularBlockMap a d R (b, x, h) : lowerTriangularSubgroup (a + d) R`:
  the element `lowerBlockPair b.val x h`. Simp lemma
  `lowerTriangularBlockMap_val`.
- `lowerTriangularBlockEquiv a d R`: `lowerTriangularBlockMap` as an
  equivalence of types. Its inverse is
  `k ↦ (lowerTriangularFirstBlock k, lowerTriangularRectangle k, lowerTriangularLastBlock k)`.
- `lowerTriangularBlockHomeomorph a d R`: the same equivalence as a
  homeomorphism, for `[TopologicalSpace R] [IsTopologicalRing R]`. Simp lemma
  `lowerTriangularBlockHomeomorph_apply`.

## Theorems

Algebra (every commutative ring `R`, all `a d : ℕ`):

- `lowerBlockPair_mem_lowerTriangularSubgroup`: if `g` is lower triangular,
  then `lowerBlockPair g x h` is lower triangular. Proof: case split on the
  two index blocks with `Fin.addCases`. The upper right block is zero, and
  the diagonal blocks are lower triangular. The case "row in the last block,
  column in the first block, row < column" cannot occur.
- `lowerTriangular_apply_castAdd_natAdd`: the upper right `a × d` block of a
  lower triangular `(a+d) × (a+d)` matrix vanishes.
- `lowerTriangular_mul_apply_castAdd`: for `k` lower triangular and any
  matrix `M`, row `i` of the first block of `k * M` is
  `∑_{l < a} k (i, l) M (l, j)`. Proof: split the sum with
  `Fin.sum_univ_add`; the terms with `l` in the last block vanish.
- `mul_lowerTriangular_apply_natAdd`: dually, column `j` of the last block of
  `M * k` is `∑_{l ∈ last block} M (i, l) k (l, j)`.
- `lowerBlockPair_mul_lowerBlockPair`:
  `lowerBlockPair g x h * lowerBlockPair g' x' h' =
   lowerBlockPair (g g') (x g' + h x') (h h')`. Proof: transport to
  `Matrix.fromBlocks` with `Matrix.submatrix_mul_equiv`, then
  `Matrix.fromBlocks_multiply`.
- `lowerTriangularBlockMap_mul`: the group law in block coordinates,
  `θ(b, x, h) · θ(b', x', h') = θ(b b', x b' + h x', h h')`, where `θ` is
  `lowerTriangularBlockMap a d R`.

Topology (`[TopologicalSpace R] [IsTopologicalRing R]`):

- `continuous_lowerTriangularBlockMap`: `θ` is continuous. This follows from
  the published `continuous_lowerBlockPair`.
- `continuous_lowerTriangularBlockEquiv_symm`: the inverse is continuous,
  since the block entries of `k` and of `k⁻¹` are continuous
  (`Units.continuous_iff`, `Continuous.matrix_submatrix`).

## Use

The proof of `LowerBlockQuotientDisintegrationStatement` uses `θ` to compare
the weighted product measure on `B̄_a × M_{d×a} × B̄_d` with a right Haar
measure on `B̄_{a+d}`. Right multiplication by `θ(g, y, h₀)` in coordinates
is `(b, x, h) ↦ (b g, x g + h y, h h₀)`, by `lowerTriangularBlockMap_mul`.
