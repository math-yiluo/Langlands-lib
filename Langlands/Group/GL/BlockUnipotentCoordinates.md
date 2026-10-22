# Rectangular block coordinates on the block unipotent radical

Author: Worker 53.

This module parametrizes the published radical `B.unipotentRadical R` of
[`Blocks`](Blocks.md) by its strictly upper rectangular blocks. It builds the
actual inverse matrix `1 + X`, proves the algebraic laws that hold in these
coordinates, and constructs the homeomorphism for a topological commutative
ring. It changes no existing Library pair. `Blocks` and `PadicBlocks` are imported
and their declarations are used by Lean name.

## Coordinate space

Let `B : BlockShape n` have `r = B.length` blocks of sizes `n_i = B.size i`.
`B.UpperPair` is the subtype of pairs `(i, j)` in `Fin r × Fin r` with `i < j`.
`B.RadicalCoordinates R` is the finite dependent product over these pairs of the
rectangular matrices `Matrix (Fin n_i) (Fin n_j) R`. In other words, one scalar
for each block pair `i < j` and each position `(a, b)` in that block. It is an
ordinary Pi type with its pointwise additive group and its product topology. The
module does not equip it with any group law transported from the radical.

The shape is arbitrary: empty shapes, one-block shapes and rank zero need no
separate treatment. `isEmpty_upperPair` shows that the coordinate space has no
index pair when `B.length ≤ 1`. Then the coordinate space is a one-point type,
and `subsingleton_unipotentRadical` shows that the radical is trivial.

## The matrix `1 + X`

`sigmaRadicalMatrix X` is the matrix on the block index type `B.Index` with
three kinds of entry. A diagonal entry `(x, x)` is `1`. An entry
`(⟨i, a⟩, ⟨j, b⟩)` with `i < j` is `X_ij a b`. Every other entry is `0`. It is
upper block triangular for `Sigma.fst`, and each of its diagonal blocks is the
identity matrix. Mathlib's `BlockTriangular.det` therefore gives determinant `1`.
`sigmaRadicalUnit X` is this matrix as a unit whose inverse is its adjugate.
The two inverse laws are `mul_adjugate` and `adjugate_mul` with determinant `1`.

`radicalMatrix X` transports this unit to `GL_n(R)` by the published
`reindex B.indexEquiv`. It is the matrix `1 + X` in the standard `Fin n`
coordinates. Its entries are given through `B.index`:

- `radicalMatrix_apply_upper`: for `i < j`, the entry at `(B.index i a, B.index j b)` is `X_ij a b`;
- `radicalMatrix_apply_same`: on a diagonal block, the entry at `(B.index i a, B.index i b)` is `1` when `a = b` and `0` otherwise;
- `radicalMatrix_apply_lower`: for `j < i`, the entry at `(B.index i a, B.index j b)` is `0`.

`det_radicalMatrix` proves determinant `1`. `radicalMatrix_inv` identifies the
inverse in `GL_n(R)` with the adjugate. `radicalMatrix_mem_parabolic` checks the
published `mem_parabolic_iff` using the lower-block zeros.
`radicalMatrix_mem_unipotentRadical` checks the published `mem_unipotentRadical_iff`
using the identity diagonal blocks. No property of the radical beyond these two
published membership characterizations is used.

## The coordinate equivalence

`radicalCoordinates : B.unipotentRadical R ≃ B.RadicalCoordinates R` sends `u` to
the blocks `(i, j) ↦ (a, b) ↦ u (B.index i a) (B.index j b)` with `i < j`. Its
inverse sends `X` to `radicalMatrix X` with the two membership proofs.
`right_inv` is the upper entry formula. For `left_inv`, both matrices are compared
entrywise after writing each index as `B.indexEquiv ⟨i, a⟩`, by trichotomy on the
blocks. Above the diagonal the entries agree by definition. On the diagonal blocks
both are Kronecker deltas, by `radicalMatrix_apply_same` and radical membership.
Below the diagonal both vanish, by `radicalMatrix_apply_lower` and parabolic
membership.

The equivalence is a bijection of types, not a group isomorphism with the additive
coordinate group. The group law in coordinates is the triangular formula below.

Formulas exposed:

- `radicalCoordinates_apply` (forward entry formula, by `rfl`);
- `radicalCoordinates_symm_apply_val`: the inverse is `radicalMatrix X` as an element of `GL_n(R)`;
- `radicalCoordinates_symm_apply_upper`, `_same`, `_lower`: the inverse entry formulas for its entries in all three block positions;
- `radicalCoordinates_one` and `radicalCoordinates_symm_zero`: the identity has zero coordinates, and zero coordinates give the identity.

## Triangular multiplication and inversion

`radicalCoordinates_mul` states, for `u, v` in the radical and `i < j`,

`(u v)_ij = u_ij + v_ij + ∑_{k : i < k < j} u_ik v_kj`,

as an equality of `n_i × n_j` matrices. The sum is over the subtype
`{k : Fin r // i < k ∧ k < j}`. The proof expands the matrix product entry
`(u v)(B.index i a, B.index j b)` as a sum over blocks `k` and positions `c`
(through `B.indexEquiv.sum_comp` and `Fintype.sum_sigma`). It evaluates each block
term by trichotomy of `k` against `i` and `j`. Blocks `k < i` and `k > j` vanish by
the parabolic zeros. The block `k = i` gives `v_ij` and the block `k = j` gives
`u_ij`, by the Kronecker diagonal blocks. The blocks `i < k < j` give
`(u_ik v_kj) a b`. A private lemma converts the remaining dependent `if` sum into
the subtype sum.

`radicalCoordinates_inv` is the resulting recursion

`(u⁻¹)_ij = -u_ij - ∑_{k : i < k < j} u_ik (u⁻¹)_kj`.

It is the multiplication formula for `u u⁻¹ = 1` together with
`radicalCoordinates_one`. `radicalCoordinates_symm_mul_symm` is the multiplication
formula for `(1 + X)(1 + Y)`, written directly in the coordinates `X`, `Y`. A
translation by a fixed radical element therefore changes the `(i, j)` coordinate
by a constant plus terms in coordinates of strictly smaller block distance. This is
the triangular form that a later Haar-measure argument can use. That argument is
not part of this module.

## Levi action

`radicalCoordinates_leviAction` states, for `m` in the product Levi `B.Levi R` and
every pair `i < j`,

`coord(B.leviAction R m u)_ij = (m i).val * coord(u)_ij * ((m j)⁻¹).val`.

Here `B.leviAction R m u` is the published conjugation `m u m⁻¹`. The proof unfolds
it to the matrix product `leviEmbedding m * u * (leviEmbedding m)⁻¹` in `GL_n(R)`.
It uses that the inverse of `leviEmbedding m` is `leviEmbedding m⁻¹` (`map_inv`).
Each multiplication by the block-diagonal matrix keeps only one block, by the
published `leviEmbedding_apply_same` and `leviEmbedding_apply_ne`. At the block
`(i, j)`, what remains is the product of `m i`, the block `u_ij` and `(m j)⁻¹`.
`radicalCoordinates_leviAction_symm` is the same formula for the radical element
with coordinates `X`.

## Topology

For `[TopologicalSpace R]`, `continuous_radicalCoordinates` proves continuity of the
forward map. The radical carries its actual published topology, the subspace
topology of the parabolic, itself a subspace of the units topology of `GL_n(R)`.
Each coordinate is the published continuous entry map `GeneralLinear.entry`
composed with the two subtype inclusions. This direction needs no continuity of the
ring operations.

With `[IsTopologicalRing R]`, `continuous_radicalCoordinates_symm` proves continuity
of the inverse. A map into units is continuous when both the matrix and its inverse
are continuous (`Units.continuous_iff`). The matrix `sigmaRadicalMatrix X` has
continuous entries: constants or coordinate evaluations. Its inverse is the
adjugate, continuous by Mathlib's `Continuous.matrix_adjugate`. The adjugate is a
polynomial in the entries. It plays the role of the finite inverse polynomial of a
unipotent matrix. Composing with the published continuous reindexing
`reindexContinuous B.indexEquiv` and the two subtype constructions gives continuity
into the radical.

`radicalCoordinatesHomeomorph : B.unipotentRadical R ≃ₜ B.RadicalCoordinates R` packages
both directions. Its hypotheses are exactly a commutative ring with a topology
making it a topological ring. `radicalCoordinatesHomeomorph_apply` and
`_symm_apply` identify its maps with the equivalence.

For a supplied p-adic realization `T : F.TopologicalData`,
`Langlands.PadicField.TopologicalData.blockRadicalCoordinates T B` is this
homeomorphism under `letI := T.topology`. This is the radical topology selected in
`PadicBlocks` (`T.unipotentRadicalTopology B`) and in
`Langlands.GLBlockModulusHaarStatement`. Lean infers the topological-ring instance
from `T.topology`, `T.valuativeRel` and `T.localField`. These are installed
locally, as in `T.blockDecomposition` of `PadicBlocks`.
`blockRadicalCoordinates_toEquiv` proves that its underlying equivalence is
`radicalCoordinates`. No new topology is chosen.

## Scope

This module does not prove Haar-measure invariance, determinant or modulus scaling,
or any measurability statement. Local compactness of the radical is the published
`B.unipotentRadicalLocallyCompactSpace` and `T.unipotentRadicalLocallyCompactSpace`,
and it is not repeated here.

## Provenance

The conventions are those of `Blocks`: ordered positive blocks, upper block
triangular parabolics, block-diagonal Levi factors and upper block unipotent
radicals. These follow Bernstein--Zelevinsky (1977), Section 2.1 and Example 2.2,
printed page 446 (PDF page 7). For `G = GL(n, F)` that example takes the standard
subgroups to be the block-diagonal subgroups attached to ordered partitions of `n`,
with parabolic triples `P = MU`. This passage was re-read for this module.

The coordinate map itself is an internal realization of the existing radical. It
writes the elementary fact that an upper block unipotent matrix is determined by
its strictly upper blocks, together with the block-matrix formulas for products and
conjugation by block-diagonal matrices. The source states none of these formulas.
They are derived here with Mathlib and proved in full. The choice of adjugate
inverse, the commutative-ring generality and the topological proofs are
implementation choices of this module.

Sources:

- `bernstein-zelevinsky-1977-induced-i`, Section 2.1 and Example 2.2, printed page 446 (PDF page 7).
  SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
