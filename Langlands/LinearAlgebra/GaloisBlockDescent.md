# Blockwise Hilbert 90 for matrix cocycles

This internal linear algebra module refines the published matrix Hilbert 90
(`Langlands.LinearAlgebra.GaloisVectorDescent.exists_matrix_coboundary`) to
cocycles with a fixed block shape. It is derived from that theorem: a
block-diagonal cocycle is a family of cocycles, one for each block, and
trivialising each block separately gives a trivialising matrix of the same block
shape. The result is a standard consequence of Hilbert 90. It was requested for
the proof of the Hermitian presentation of rank-one outer type A groups, where a
Galois cocycle is corrected without leaving the centraliser of a diagonal torus.

The setting is that of `GaloisVectorDescent`: fields `k` and `L` in one
universe, an algebra `k → L`, and a finite subgroup `H` of the `k`-algebra
automorphisms of `L`. The fields may have any characteristic, and `L/k` need not
be finite or Galois. For an automorphism `σ` and a matrix `M`, `σ(M)` is `M`
with `σ` applied to every entry (`M.map σ`, or
`Matrix.GeneralLinearGroup.map σ` for invertible matrices).

The block shape is given by a label function `w : I → B`. Here `I` is a finite
index type with decidable equality, and `B` is any type in an independent
universe; `B` may be infinite and needs no decidable equality. A matrix has the
block shape of `w` when its `(i, j)` entry is zero whenever `w i ≠ w j`.

## Statements

- `exists_blockDiagonal'_coboundary` (block-diagonal form): let `o` be a finite
  type with decidable equality and `m : o → Type` a family of finite types with
  decidable equality. Let `c : H → ∀ b, Matrix (m b) (m b) L` be a family of
  matrix cocycles, meaning `c 1 b = 1` and `c (σ τ) b = c σ b * σ(c τ b)` for
  every block `b`. Then there are `P b : GL (m b) L` and `Q : GL (Σ b, m b) L`
  whose underlying matrix is `blockDiagonal' (fun b => P b)`, such that
  `blockDiagonal' (c σ) * σ(Q) = Q` for every `σ`.
- `exists_blockwise_matrix_coboundary` (the main statement): let
  `c : H → Matrix I I L` satisfy `c 1 = 1` and the cocycle law
  `c (σ τ) = c σ * σ(c τ)`, and suppose `c σ i j = 0` whenever `w i ≠ w j`, for
  every `σ`. Then there is `P : GL I L` with `c σ * σ(P) = P` for every `σ` and
  with `P i j = 0` whenever `w i ≠ w j`.
- `blockCoboundaryMatrix` (the selected definition): the noncomputable choice, by
  `Classical.choose`, of a matrix `P : GL I L` as in
  `exists_blockwise_matrix_coboundary`. It takes the label function, the
  cocycle, and proofs of the three hypotheses. It is not canonical.
  `blockCoboundaryMatrix_spec` records `c σ * σ(P) = P`,
  `blockCoboundaryMatrix_apply_of_ne` records `P i j = 0` when `w i ≠ w j`, and
  `eq_blockCoboundaryMatrix_mul` records the coboundary form
  `c σ = P * σ(P⁻¹)` for this choice.
- `exists_blockwise_coboundary` (the same statement for `GL`-valued
  cocycles): let `c : H → GL I L` satisfy `c 1 = 1` and
  `c (σ τ) = c σ * GL.map σ (c τ)`, and have zero entries `c σ i j` whenever
  `w i ≠ w j`. Then there is `P : GL I L` with `c σ * GL.map σ P = P` for every
  `σ` and with `P i j = 0` whenever `w i ≠ w j`.

As in `GaloisVectorDescent`, the matrix-valued cocycle need not have invertible
values; invertibility follows from the conclusion.

## Proofs

For the block-diagonal form, `P b` is the published `coboundaryMatrix` of the
`b`-th cocycle. The block-diagonal matrix of the `P b` is invertible, with
inverse the block-diagonal matrix of the `(P b)⁻¹`. This holds because
`blockDiagonal'` is multiplicative (`blockDiagonal'_mul`) and sends the identity
family to the identity (`blockDiagonal'_one`). Applying `σ` commutes with
`blockDiagonal'` (`blockDiagonal'_map`), so `blockDiagonal' (c σ) * σ(Q)` is the
block-diagonal matrix of the products `c σ b * σ(P b)`. Each such product equals
`P b` by `coboundaryMatrix_spec`.

For the main statement, let `w'` be `w` with its codomain restricted to the
range of `w` (`Set.rangeFactorization`). This range is finite because `I` is.
Then `w' i = w' j` exactly when `w i = w j`. The equivalence
`e := Equiv.sigmaFiberEquiv w'` identifies `Σ b, {i // w' i = b}` with `I`.
Reindexing by `e` turns each `c σ` into the block-diagonal matrix of its
diagonal blocks `c σ` restricted to the fibres. The reason is that the
off-diagonal-block entries vanish by hypothesis. Reindexing by an equivalence is
multiplicative (`Matrix.submatrix_mul_equiv`) and commutes with applying `σ`,
and `blockDiagonal'` is injective. Hence the cocycle law for `c` gives the
cocycle law for each block, and the identity law likewise gives `1` on each
block. The block-diagonal form then gives `Q`, and `P` is `Q` reindexed back
along `e⁻¹`, with inverse `Q⁻¹` reindexed the same way. The equation
`c σ * σ(P) = P` is checked after reindexing by `e`, where it is the equation for
`Q`. The entry `P i j` is the entry of `Q` at the pair of fibre positions of `i`
and `j`. When `w i ≠ w j` these lie in different blocks, so the entry is zero by
`blockDiagonal'_apply_ne`.

The definition and its three lemmas are the choice specification and, for the
coboundary form, the published `eq_mul_map_inv_of_mul_map_eq`. The `GL` form
applies the main statement to the underlying matrices. This works because the
underlying matrix of `GL.map σ g` is `σ(g)` by definition, and a unit is
determined by its underlying matrix (`Units.ext`).

## Scope

This module supplies no group scheme, torus, or Hermitian form. As motivation
only: when `w i` records the character by which a diagonal torus acts on the
`i`-th coordinate, and distinct labels are distinct characters, the block shape
of `w` is the zero pattern of matrices commuting with that torus. The module
itself states nothing about tori.
