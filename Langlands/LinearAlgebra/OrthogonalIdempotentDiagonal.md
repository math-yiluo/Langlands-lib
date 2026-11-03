# Simultaneous diagonalization of orthogonal idempotent matrices

Worker 303. This module proves one linear-algebra theorem,
`Langlands.LinearAlgebra.exists_conj_eq_diagonal_of_orthogonal`. It is used
by `Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterWeights` to
conjugate a cocharacter of `GL_n` over a field to a diagonal cocharacter.

## Statement

Take a field `K`, a finite type `n` with decidable equality, an index type
`ι` with decidable equality, and a family of square matrices
`E : ι → Matrix n n K`. Assume two things:

- the matrices are orthogonal idempotents:
  `E a * E b = if a = b then E a else 0` for all `a`, `b`;
- for some finite set `s : Finset ι`, their sum over `s` is `1`.

Then there are an invertible matrix `P` and a labelling `e : n → ι` such that,
for every `a`, `P⁻¹ * E a * P` is the diagonal matrix whose entry at `i` is
`1` when `e i = a` and `0` otherwise.

No assumption is made on `ι` beyond decidable equality. Indices outside `s`
are allowed: the hypotheses force the corresponding matrices to vanish, and
they then occur in no label.

## Proof

Let `W a` be the range of the linear map of `E a` on `n → K`.

- Since `E b` is idempotent, it fixes every vector of `W b`. For `a ≠ b`,
  `E a` kills `W b`, because `E a * E b = 0`.
- Hence `W a` is disjoint from the sum of the `W b` with `b ≠ a`. A vector in
  both is fixed by `E a` and killed by it. So the family `W` is independent
  (`iSupIndep`).
- Every vector `x` equals `∑ a ∈ s, E a x`, so the `W a` span the whole space.
- Mathlib's `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`
  therefore makes the family `W` an internal direct sum.
- The collected basis of chosen bases `Basis.ofVectorSpace` of the `W a`
  (`DirectSum.IsInternal.collectedBasis`) is a basis of `n → K`. Its index
  type is in bijection with `n` (`Basis.indexEquiv`). Reindexing gives a basis
  `B'` indexed by `n`, and the label `e i` is the summand containing `B' i`.
- `P` is the matrix with columns `B' i` (`Basis.toMatrix` from the standard
  basis). Its inverse is the transition matrix in the other direction
  (`Basis.toMatrix_mul_toMatrix_flip`).
- Column by column, `E a * P = P * D_a`, where `D_a` is the stated diagonal
  matrix. Indeed, `E a` fixes `B' i` when `e i = a` and kills it otherwise.
  Multiplying on the left by `P⁻¹` gives the claim.

## Source

This is the linear-algebra step in the proof of Milne, *Algebraic Groups*
(2017), source ID `milne-2017-algebraic-groups`, Theorem 12.12 (printed
pp.234–235, PDF pp.250–251). There, a representation of a diagonalizable group
decomposes into weight spaces, and a basis adapted to the decomposition
diagonalizes it. The theorem here isolates that step for an arbitrary family
of orthogonal idempotents. Its Lean proof is the direct argument above.
