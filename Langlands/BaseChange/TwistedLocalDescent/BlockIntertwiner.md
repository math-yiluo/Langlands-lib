# Intertwiners of block upper triangular matrices

Module `Langlands.BaseChange.TwistedLocalDescent.BlockIntertwiner`.

- `intertwiner_eq_zero`: over a field, if `A X = X C` for square matrices `A` (size `a`), `C`
  (size `b`) and a rectangular `X`, and the characteristic polynomials of `A` and `C` are coprime,
  then `X = 0` (Sylvester's argument: `χ_C(A) X = X χ_C(C) = 0` and `χ_C(A)` is invertible).
- `block B A i j`: the `(i, j)` block of a square matrix for the block shape `B`;
  `IsBlockUpper B A`: all blocks strictly below the diagonal vanish;
  `isBlockUpper_iff_mem_parabolic`: for `g ∈ GL_n`, this is membership in the standard block
  parabolic.
- `isBlockUpper_of_mul_eq` (**block intertwiner lemma**, over a field): let `A`, `C` be block
  upper triangular with `G A = C G`, and suppose that for all distinct block indices `k ≠ i` the
  characteristic polynomials of the diagonal blocks `C_kk` and `A_ii` are coprime. Then `G` is
  block upper triangular. Proof by strong induction on `i + (length − k)` over the blocks
  `(k, i)` with `i < k`, i.e. starting from the bottom left corner: in the block `(k, i)` of
  `G A = C G`, the blocks of `G` in the same row farther left and in the same column farther down
  vanish by the induction hypothesis, leaving `G_ki A_ii = C_kk G_ki`, so `G_ki = 0` by
  `intertwiner_eq_zero`.
