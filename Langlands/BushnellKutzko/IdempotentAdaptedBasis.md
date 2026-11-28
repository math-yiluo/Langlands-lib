# Two-block parabolics attached to an idempotent

The module `Langlands.BushnellKutzko.IdempotentAdaptedBasis` (namespace
`Langlands.BushnellKutzko.BlockIdempotent`) relates the unipotent radical `upperGroup ε` of an
idempotent `ε` of `End_F(F^n)` (module `IdempotentIwahoriFactorization`) to the conjugated
standard unipotent radicals `B.conjugateUnipotent g` of `GL_n(F)`.

- `exists_adapted_basis`: if the range of `ε` on `F^(a+c)` has dimension `a`, there is a basis
  whose first `a` vectors lie in the range of `ε` and whose last `c` vectors lie in its
  kernel. It is assembled from bases of the range and the kernel, which are complementary
  because `ε` is idempotent.
- `exists_conj_mem_upperGroup`: for such `ε` there is `g ∈ GL_(a+c)(F)` (the change of basis
  to an adapted basis) such that `toLin (g X g⁻¹) ∈ upperGroup ε` for every block unipotent
  matrix `X = [[1_a, *], [0, 1_c]]` (`IsBlockUnipotent a X`). The proof evaluates on the
  adapted basis: `X` fixes the first `a` standard vectors and is the identity modulo them.
- `exists_blockShape`: for an idempotent `ε` of `F^n` with `ε ≠ 0` and `ε ≠ 1` there are a
  block shape `B` with `B.parabolic F ≠ ⊤` and `g ∈ GL_n(F)` such that every element of
  `B.conjugateUnipotent g` maps into `upperGroup ε` under `toLin`. Here `B` is the two-block
  shape `BlockShape.binary a c` with `a = dim range ε` and `c = dim ker ε`, both positive;
  properness is `binary_parabolic_ne_top`, and `isBlockUnipotent_of_mem_binary` identifies its
  unipotent radical with the block unipotent matrices.
